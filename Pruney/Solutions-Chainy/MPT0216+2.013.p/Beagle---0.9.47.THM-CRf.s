%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:45 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   41 (  64 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 (  69 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k1_tarski(A) = k2_tarski(B,C)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_18,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    ! [B_20,A_21,C_22] :
      ( B_20 = A_21
      | k2_tarski(B_20,C_22) != k1_tarski(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_21] :
      ( A_21 = '#skF_2'
      | k1_tarski(A_21) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_41])).

tff(c_102,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_47])).

tff(c_16,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_16])).

tff(c_105,plain,(
    k2_tarski('#skF_1','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(C_37)) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_188,plain,(
    ! [A_11,C_37] : k2_xboole_0(k1_tarski(A_11),k1_tarski(C_37)) = k1_enumset1(A_11,A_11,C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_176])).

tff(c_191,plain,(
    ! [A_11,C_37] : k2_xboole_0(k1_tarski(A_11),k1_tarski(C_37)) = k2_tarski(A_11,C_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_185,plain,(
    ! [C_37] : k2_xboole_0(k1_tarski('#skF_1'),k1_tarski(C_37)) = k1_enumset1('#skF_1','#skF_3',C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_176])).

tff(c_202,plain,(
    ! [C_40] : k1_enumset1('#skF_1','#skF_3',C_40) = k2_tarski('#skF_1',C_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_185])).

tff(c_48,plain,(
    ! [C_23,B_24,A_25] : k1_enumset1(C_23,B_24,A_25) = k1_enumset1(A_25,B_24,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [C_23,B_24] : k1_enumset1(C_23,B_24,B_24) = k2_tarski(B_24,C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_209,plain,(
    k2_tarski('#skF_3','#skF_1') = k2_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_64])).

tff(c_232,plain,(
    k2_tarski('#skF_3','#skF_1') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_209])).

tff(c_14,plain,(
    ! [B_15,A_14,C_16] :
      ( B_15 = A_14
      | k2_tarski(B_15,C_16) != k1_tarski(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_241,plain,(
    ! [A_14] :
      ( A_14 = '#skF_3'
      | k1_tarski(A_14) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_14])).

tff(c_249,plain,(
    '#skF_3' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_241])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.13  
% 1.70/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.13  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.70/1.13  
% 1.70/1.13  %Foreground sorts:
% 1.70/1.13  
% 1.70/1.13  
% 1.70/1.13  %Background operators:
% 1.70/1.13  
% 1.70/1.13  
% 1.70/1.13  %Foreground operators:
% 1.70/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.70/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.13  
% 1.70/1.14  tff(f_46, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.70/1.14  tff(f_41, axiom, (![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.70/1.14  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.70/1.14  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.70/1.14  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.70/1.14  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 1.70/1.14  tff(c_18, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.14  tff(c_41, plain, (![B_20, A_21, C_22]: (B_20=A_21 | k2_tarski(B_20, C_22)!=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.70/1.14  tff(c_47, plain, (![A_21]: (A_21='#skF_2' | k1_tarski(A_21)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_41])).
% 1.70/1.14  tff(c_102, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_47])).
% 1.70/1.14  tff(c_16, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.14  tff(c_106, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_16])).
% 1.70/1.14  tff(c_105, plain, (k2_tarski('#skF_1', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_18])).
% 1.70/1.14  tff(c_12, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.14  tff(c_10, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.14  tff(c_176, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(C_37))=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.14  tff(c_188, plain, (![A_11, C_37]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(C_37))=k1_enumset1(A_11, A_11, C_37))), inference(superposition, [status(thm), theory('equality')], [c_10, c_176])).
% 1.70/1.14  tff(c_191, plain, (![A_11, C_37]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(C_37))=k2_tarski(A_11, C_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188])).
% 1.70/1.14  tff(c_185, plain, (![C_37]: (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski(C_37))=k1_enumset1('#skF_1', '#skF_3', C_37))), inference(superposition, [status(thm), theory('equality')], [c_105, c_176])).
% 1.70/1.14  tff(c_202, plain, (![C_40]: (k1_enumset1('#skF_1', '#skF_3', C_40)=k2_tarski('#skF_1', C_40))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_185])).
% 1.70/1.14  tff(c_48, plain, (![C_23, B_24, A_25]: (k1_enumset1(C_23, B_24, A_25)=k1_enumset1(A_25, B_24, C_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.14  tff(c_64, plain, (![C_23, B_24]: (k1_enumset1(C_23, B_24, B_24)=k2_tarski(B_24, C_23))), inference(superposition, [status(thm), theory('equality')], [c_48, c_12])).
% 1.70/1.14  tff(c_209, plain, (k2_tarski('#skF_3', '#skF_1')=k2_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_202, c_64])).
% 1.70/1.14  tff(c_232, plain, (k2_tarski('#skF_3', '#skF_1')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_209])).
% 1.70/1.14  tff(c_14, plain, (![B_15, A_14, C_16]: (B_15=A_14 | k2_tarski(B_15, C_16)!=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.70/1.14  tff(c_241, plain, (![A_14]: (A_14='#skF_3' | k1_tarski(A_14)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_14])).
% 1.70/1.14  tff(c_249, plain, ('#skF_3'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_241])).
% 1.70/1.14  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_249])).
% 1.70/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  Inference rules
% 1.70/1.14  ----------------------
% 1.70/1.14  #Ref     : 3
% 1.70/1.14  #Sup     : 55
% 1.70/1.14  #Fact    : 0
% 1.70/1.14  #Define  : 0
% 1.70/1.14  #Split   : 0
% 1.70/1.14  #Chain   : 0
% 1.70/1.14  #Close   : 0
% 1.70/1.14  
% 1.70/1.14  Ordering : KBO
% 1.70/1.14  
% 1.70/1.14  Simplification rules
% 1.70/1.14  ----------------------
% 1.70/1.14  #Subsume      : 2
% 1.70/1.14  #Demod        : 20
% 1.70/1.14  #Tautology    : 43
% 1.70/1.14  #SimpNegUnit  : 1
% 1.70/1.14  #BackRed      : 3
% 1.70/1.14  
% 1.70/1.14  #Partial instantiations: 0
% 1.70/1.14  #Strategies tried      : 1
% 1.70/1.14  
% 1.70/1.14  Timing (in seconds)
% 1.70/1.14  ----------------------
% 1.70/1.15  Preprocessing        : 0.27
% 1.70/1.15  Parsing              : 0.14
% 1.70/1.15  CNF conversion       : 0.02
% 1.70/1.15  Main loop            : 0.15
% 1.70/1.15  Inferencing          : 0.06
% 1.70/1.15  Reduction            : 0.05
% 1.70/1.15  Demodulation         : 0.04
% 1.70/1.15  BG Simplification    : 0.01
% 1.70/1.15  Subsumption          : 0.02
% 1.70/1.15  Abstraction          : 0.01
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.44
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.15  Index Matching       : 0.00
% 1.70/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
