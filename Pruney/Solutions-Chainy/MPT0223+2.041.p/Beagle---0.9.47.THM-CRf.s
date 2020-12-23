%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k3_xboole_0(B_23,A_22)) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_109,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_96])).

tff(c_144,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | k2_xboole_0(k1_tarski(A_26),k1_tarski(B_25)) != k1_tarski(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_144])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.32  
% 1.96/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.32  %$ k2_enumset1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.96/1.32  
% 1.96/1.32  %Foreground sorts:
% 1.96/1.32  
% 1.96/1.32  
% 1.96/1.32  %Background operators:
% 1.96/1.32  
% 1.96/1.32  
% 1.96/1.32  %Foreground operators:
% 1.96/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.32  
% 1.96/1.33  tff(f_46, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.96/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.96/1.33  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.96/1.33  tff(f_41, axiom, (![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.96/1.33  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.33  tff(c_18, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.33  tff(c_61, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.33  tff(c_96, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k3_xboole_0(B_23, A_22))=A_22)), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 1.96/1.33  tff(c_109, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_96])).
% 1.96/1.33  tff(c_144, plain, (![B_25, A_26]: (B_25=A_26 | k2_xboole_0(k1_tarski(A_26), k1_tarski(B_25))!=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.33  tff(c_147, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_109, c_144])).
% 1.96/1.33  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_147])).
% 1.96/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.33  
% 1.96/1.33  Inference rules
% 1.96/1.33  ----------------------
% 1.96/1.33  #Ref     : 0
% 1.96/1.33  #Sup     : 34
% 1.96/1.33  #Fact    : 0
% 1.96/1.33  #Define  : 0
% 1.96/1.33  #Split   : 0
% 1.96/1.33  #Chain   : 0
% 1.96/1.33  #Close   : 0
% 1.96/1.33  
% 1.96/1.33  Ordering : KBO
% 1.96/1.33  
% 1.96/1.33  Simplification rules
% 1.96/1.33  ----------------------
% 1.96/1.33  #Subsume      : 0
% 1.96/1.33  #Demod        : 5
% 1.96/1.33  #Tautology    : 29
% 1.96/1.33  #SimpNegUnit  : 1
% 1.96/1.33  #BackRed      : 0
% 1.96/1.33  
% 1.96/1.33  #Partial instantiations: 0
% 1.96/1.33  #Strategies tried      : 1
% 1.96/1.33  
% 1.96/1.33  Timing (in seconds)
% 1.96/1.33  ----------------------
% 1.96/1.33  Preprocessing        : 0.40
% 1.96/1.33  Parsing              : 0.23
% 1.96/1.33  CNF conversion       : 0.02
% 1.96/1.33  Main loop            : 0.12
% 1.96/1.33  Inferencing          : 0.05
% 1.96/1.33  Reduction            : 0.04
% 1.96/1.33  Demodulation         : 0.03
% 1.96/1.33  BG Simplification    : 0.01
% 1.96/1.33  Subsumption          : 0.02
% 1.96/1.33  Abstraction          : 0.01
% 1.96/1.33  MUC search           : 0.00
% 1.96/1.33  Cooper               : 0.00
% 1.96/1.33  Total                : 0.54
% 1.96/1.33  Index Insertion      : 0.00
% 1.96/1.33  Index Deletion       : 0.00
% 1.96/1.33  Index Matching       : 0.00
% 1.96/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
