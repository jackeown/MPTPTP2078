%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:40 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_10])).

tff(c_109,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | k2_xboole_0(k1_tarski(A_31),k1_tarski(B_30)) != k1_tarski(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | k2_xboole_0(k1_tarski(B_37),k1_tarski(A_38)) != k1_tarski(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_130,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_127])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.51  
% 2.15/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.51  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.51  
% 2.15/1.51  %Foreground sorts:
% 2.15/1.51  
% 2.15/1.51  
% 2.15/1.51  %Background operators:
% 2.15/1.51  
% 2.15/1.51  
% 2.15/1.51  %Foreground operators:
% 2.15/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.51  
% 2.15/1.52  tff(f_52, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.15/1.52  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.52  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.52  tff(f_47, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.15/1.52  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.52  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.52  tff(c_80, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.52  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.52  tff(c_105, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_10])).
% 2.15/1.52  tff(c_109, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22, c_105])).
% 2.15/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.52  tff(c_98, plain, (![B_30, A_31]: (B_30=A_31 | k2_xboole_0(k1_tarski(A_31), k1_tarski(B_30))!=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.52  tff(c_127, plain, (![B_37, A_38]: (B_37=A_38 | k2_xboole_0(k1_tarski(B_37), k1_tarski(A_38))!=k1_tarski(A_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 2.15/1.52  tff(c_130, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_109, c_127])).
% 2.15/1.52  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_130])).
% 2.15/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.52  
% 2.15/1.52  Inference rules
% 2.15/1.52  ----------------------
% 2.15/1.52  #Ref     : 0
% 2.15/1.52  #Sup     : 29
% 2.15/1.52  #Fact    : 0
% 2.15/1.52  #Define  : 0
% 2.15/1.52  #Split   : 0
% 2.15/1.52  #Chain   : 0
% 2.15/1.52  #Close   : 0
% 2.15/1.52  
% 2.15/1.52  Ordering : KBO
% 2.15/1.52  
% 2.15/1.52  Simplification rules
% 2.15/1.52  ----------------------
% 2.15/1.52  #Subsume      : 0
% 2.15/1.52  #Demod        : 0
% 2.15/1.52  #Tautology    : 21
% 2.15/1.52  #SimpNegUnit  : 2
% 2.15/1.52  #BackRed      : 0
% 2.15/1.52  
% 2.15/1.52  #Partial instantiations: 0
% 2.15/1.52  #Strategies tried      : 1
% 2.15/1.52  
% 2.15/1.52  Timing (in seconds)
% 2.15/1.52  ----------------------
% 2.15/1.53  Preprocessing        : 0.45
% 2.15/1.53  Parsing              : 0.23
% 2.15/1.53  CNF conversion       : 0.03
% 2.15/1.53  Main loop            : 0.19
% 2.15/1.53  Inferencing          : 0.08
% 2.15/1.53  Reduction            : 0.06
% 2.15/1.53  Demodulation         : 0.04
% 2.15/1.53  BG Simplification    : 0.02
% 2.15/1.53  Subsumption          : 0.03
% 2.15/1.53  Abstraction          : 0.01
% 2.15/1.53  MUC search           : 0.00
% 2.15/1.53  Cooper               : 0.00
% 2.15/1.53  Total                : 0.68
% 2.15/1.53  Index Insertion      : 0.00
% 2.15/1.53  Index Deletion       : 0.00
% 2.15/1.53  Index Matching       : 0.00
% 2.15/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
