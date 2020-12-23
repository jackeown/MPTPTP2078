%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [B_10,A_11] : k2_xboole_0(B_10,A_11) = k2_xboole_0(A_11,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_11,B_10] : r1_tarski(A_11,k2_xboole_0(B_10,A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4])).

tff(c_76,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_76,c_8])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:28:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.13  
% 1.59/1.13  %Foreground sorts:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Background operators:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Foreground operators:
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.13  
% 1.59/1.13  tff(f_40, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.59/1.13  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.59/1.13  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.59/1.13  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.59/1.13  tff(c_10, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.13  tff(c_12, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.13  tff(c_14, plain, (![B_10, A_11]: (k2_xboole_0(B_10, A_11)=k2_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.13  tff(c_29, plain, (![A_11, B_10]: (r1_tarski(A_11, k2_xboole_0(B_10, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4])).
% 1.59/1.13  tff(c_76, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.59/1.13  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.13  tff(c_90, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_76, c_8])).
% 1.59/1.13  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_90])).
% 1.59/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  Inference rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Ref     : 0
% 1.59/1.13  #Sup     : 20
% 1.59/1.13  #Fact    : 0
% 1.59/1.13  #Define  : 0
% 1.59/1.13  #Split   : 0
% 1.59/1.13  #Chain   : 0
% 1.59/1.13  #Close   : 0
% 1.59/1.13  
% 1.59/1.13  Ordering : KBO
% 1.59/1.13  
% 1.59/1.13  Simplification rules
% 1.59/1.13  ----------------------
% 1.59/1.13  #Subsume      : 0
% 1.59/1.13  #Demod        : 3
% 1.59/1.13  #Tautology    : 16
% 1.59/1.13  #SimpNegUnit  : 1
% 1.59/1.13  #BackRed      : 0
% 1.59/1.13  
% 1.59/1.13  #Partial instantiations: 0
% 1.59/1.13  #Strategies tried      : 1
% 1.59/1.13  
% 1.59/1.13  Timing (in seconds)
% 1.59/1.13  ----------------------
% 1.59/1.14  Preprocessing        : 0.26
% 1.59/1.14  Parsing              : 0.14
% 1.59/1.14  CNF conversion       : 0.01
% 1.59/1.14  Main loop            : 0.09
% 1.59/1.14  Inferencing          : 0.04
% 1.59/1.14  Reduction            : 0.03
% 1.59/1.14  Demodulation         : 0.02
% 1.59/1.14  BG Simplification    : 0.01
% 1.59/1.14  Subsumption          : 0.01
% 1.59/1.14  Abstraction          : 0.00
% 1.59/1.14  MUC search           : 0.00
% 1.59/1.14  Cooper               : 0.00
% 1.59/1.14  Total                : 0.37
% 1.59/1.14  Index Insertion      : 0.00
% 1.59/1.14  Index Deletion       : 0.00
% 1.59/1.14  Index Matching       : 0.00
% 1.59/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
