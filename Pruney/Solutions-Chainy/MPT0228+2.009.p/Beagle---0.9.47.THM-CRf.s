%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),k1_tarski(B_14))
      | B_14 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(k2_xboole_0(A_27,B_28),B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k2_tarski(A_29,B_30),k1_tarski(B_30)) = k1_tarski(A_29)
      | ~ r1_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_82,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(k2_tarski(A_31,B_32),k1_tarski(B_32)) = k1_tarski(A_31)
      | B_32 = A_31 ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_16,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  %$ r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.14  
% 1.62/1.14  tff(f_50, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.62/1.14  tff(f_44, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.62/1.14  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.62/1.14  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.62/1.14  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.14  tff(c_14, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), k1_tarski(B_14)) | B_14=A_13)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.14  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.14  tff(c_65, plain, (![A_27, B_28]: (k4_xboole_0(k2_xboole_0(A_27, B_28), B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.14  tff(c_77, plain, (![A_29, B_30]: (k4_xboole_0(k2_tarski(A_29, B_30), k1_tarski(B_30))=k1_tarski(A_29) | ~r1_xboole_0(k1_tarski(A_29), k1_tarski(B_30)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 1.62/1.14  tff(c_82, plain, (![A_31, B_32]: (k4_xboole_0(k2_tarski(A_31, B_32), k1_tarski(B_32))=k1_tarski(A_31) | B_32=A_31)), inference(resolution, [status(thm)], [c_14, c_77])).
% 1.62/1.14  tff(c_16, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.62/1.14  tff(c_88, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_82, c_16])).
% 1.62/1.14  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_88])).
% 1.62/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  Inference rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Ref     : 0
% 1.62/1.14  #Sup     : 18
% 1.62/1.14  #Fact    : 0
% 1.62/1.14  #Define  : 0
% 1.62/1.14  #Split   : 0
% 1.62/1.14  #Chain   : 0
% 1.62/1.14  #Close   : 0
% 1.62/1.14  
% 1.62/1.14  Ordering : KBO
% 1.62/1.14  
% 1.62/1.14  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 0
% 1.62/1.15  #Demod        : 0
% 1.62/1.15  #Tautology    : 13
% 1.62/1.15  #SimpNegUnit  : 1
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.15  Preprocessing        : 0.27
% 1.62/1.15  Parsing              : 0.15
% 1.62/1.15  CNF conversion       : 0.01
% 1.62/1.15  Main loop            : 0.09
% 1.62/1.15  Inferencing          : 0.04
% 1.62/1.15  Reduction            : 0.02
% 1.62/1.15  Demodulation         : 0.01
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.01
% 1.62/1.15  Abstraction          : 0.01
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.38
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
