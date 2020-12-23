%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:45 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [C_62,B_63,A_64] : k1_enumset1(C_62,B_63,A_64) = k1_enumset1(A_64,B_63,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [C_62,B_63] : k1_enumset1(C_62,B_63,B_63) = k2_tarski(B_63,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_14])).

tff(c_12,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_298,plain,(
    ! [A_76,B_77,C_78,D_79] : k2_xboole_0(k2_tarski(A_76,B_77),k2_tarski(C_78,D_79)) = k2_enumset1(A_76,B_77,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_339,plain,(
    ! [A_20,C_78,D_79] : k2_xboole_0(k1_tarski(A_20),k2_tarski(C_78,D_79)) = k2_enumset1(A_20,A_20,C_78,D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_298])).

tff(c_355,plain,(
    ! [A_85,C_86,D_87] : k2_xboole_0(k1_tarski(A_85),k2_tarski(C_86,D_87)) = k1_enumset1(A_85,C_86,D_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_339])).

tff(c_382,plain,(
    ! [A_85,A_20] : k2_xboole_0(k1_tarski(A_85),k1_tarski(A_20)) = k1_enumset1(A_85,A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_355])).

tff(c_385,plain,(
    ! [A_85,A_20] : k2_xboole_0(k1_tarski(A_85),k1_tarski(A_20)) = k2_tarski(A_20,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_382])).

tff(c_26,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_386,plain,(
    k2_tarski('#skF_2','#skF_1') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_29])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:23:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.91/1.24  
% 1.91/1.24  %Foreground sorts:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Background operators:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Foreground operators:
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.24  
% 1.91/1.25  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.91/1.25  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 1.91/1.25  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.91/1.25  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.25  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.91/1.25  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.91/1.25  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.91/1.25  tff(f_54, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.91/1.25  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.25  tff(c_175, plain, (![C_62, B_63, A_64]: (k1_enumset1(C_62, B_63, A_64)=k1_enumset1(A_64, B_63, C_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.25  tff(c_14, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.25  tff(c_191, plain, (![C_62, B_63]: (k1_enumset1(C_62, B_63, B_63)=k2_tarski(B_63, C_62))), inference(superposition, [status(thm), theory('equality')], [c_175, c_14])).
% 1.91/1.25  tff(c_12, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.25  tff(c_16, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.25  tff(c_298, plain, (![A_76, B_77, C_78, D_79]: (k2_xboole_0(k2_tarski(A_76, B_77), k2_tarski(C_78, D_79))=k2_enumset1(A_76, B_77, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.25  tff(c_339, plain, (![A_20, C_78, D_79]: (k2_xboole_0(k1_tarski(A_20), k2_tarski(C_78, D_79))=k2_enumset1(A_20, A_20, C_78, D_79))), inference(superposition, [status(thm), theory('equality')], [c_12, c_298])).
% 1.91/1.25  tff(c_355, plain, (![A_85, C_86, D_87]: (k2_xboole_0(k1_tarski(A_85), k2_tarski(C_86, D_87))=k1_enumset1(A_85, C_86, D_87))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_339])).
% 1.91/1.25  tff(c_382, plain, (![A_85, A_20]: (k2_xboole_0(k1_tarski(A_85), k1_tarski(A_20))=k1_enumset1(A_85, A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_12, c_355])).
% 1.91/1.25  tff(c_385, plain, (![A_85, A_20]: (k2_xboole_0(k1_tarski(A_85), k1_tarski(A_20))=k2_tarski(A_20, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_382])).
% 1.91/1.25  tff(c_26, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.25  tff(c_28, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.25  tff(c_29, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 1.91/1.25  tff(c_386, plain, (k2_tarski('#skF_2', '#skF_1')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_29])).
% 1.91/1.25  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_386])).
% 1.91/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  Inference rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Ref     : 0
% 1.91/1.25  #Sup     : 89
% 1.91/1.25  #Fact    : 0
% 1.91/1.25  #Define  : 0
% 1.91/1.25  #Split   : 0
% 1.91/1.25  #Chain   : 0
% 1.91/1.25  #Close   : 0
% 1.91/1.25  
% 1.91/1.25  Ordering : KBO
% 1.91/1.25  
% 1.91/1.25  Simplification rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Subsume      : 2
% 1.91/1.25  #Demod        : 21
% 1.91/1.25  #Tautology    : 62
% 1.91/1.25  #SimpNegUnit  : 0
% 1.91/1.25  #BackRed      : 1
% 1.91/1.25  
% 1.91/1.25  #Partial instantiations: 0
% 1.91/1.25  #Strategies tried      : 1
% 1.91/1.25  
% 1.91/1.25  Timing (in seconds)
% 1.91/1.25  ----------------------
% 1.91/1.26  Preprocessing        : 0.31
% 1.91/1.26  Parsing              : 0.17
% 1.91/1.26  CNF conversion       : 0.02
% 1.91/1.26  Main loop            : 0.19
% 1.91/1.26  Inferencing          : 0.07
% 1.91/1.26  Reduction            : 0.08
% 1.91/1.26  Demodulation         : 0.06
% 1.91/1.26  BG Simplification    : 0.02
% 1.91/1.26  Subsumption          : 0.03
% 1.91/1.26  Abstraction          : 0.02
% 1.91/1.26  MUC search           : 0.00
% 1.91/1.26  Cooper               : 0.00
% 1.91/1.26  Total                : 0.53
% 1.91/1.26  Index Insertion      : 0.00
% 1.91/1.26  Index Deletion       : 0.00
% 1.91/1.26  Index Matching       : 0.00
% 1.91/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
