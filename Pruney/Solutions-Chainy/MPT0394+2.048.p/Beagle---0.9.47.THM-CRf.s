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
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   42 (  67 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   34 (  59 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k2_tarski(A_54,B_55),k1_tarski(C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_17,C_56] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_56)) = k1_enumset1(A_17,A_17,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_113,plain,(
    ! [A_57,C_58] : k2_xboole_0(k1_tarski(A_57),k1_tarski(C_58)) = k2_tarski(A_57,C_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_22,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    ! [A_59,C_60] : k2_tarski(A_59,C_60) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_22])).

tff(c_136,plain,(
    ! [A_17] : k1_tarski(A_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_134])).

tff(c_26,plain,(
    ! [A_40] : k1_setfam_1(k1_tarski(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    ! [A_17,C_56] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_56)) = k2_tarski(A_17,C_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_368,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(k1_setfam_1(A_94),k1_setfam_1(B_95)) = k1_setfam_1(k2_xboole_0(A_94,B_95))
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_377,plain,(
    ! [A_40,B_95] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_40),B_95)) = k3_xboole_0(A_40,k1_setfam_1(B_95))
      | k1_xboole_0 = B_95
      | k1_tarski(A_40) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_368])).

tff(c_755,plain,(
    ! [A_128,B_129] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_128),B_129)) = k3_xboole_0(A_128,k1_setfam_1(B_129))
      | k1_xboole_0 = B_129 ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_377])).

tff(c_785,plain,(
    ! [A_17,C_56] :
      ( k3_xboole_0(A_17,k1_setfam_1(k1_tarski(C_56))) = k1_setfam_1(k2_tarski(A_17,C_56))
      | k1_tarski(C_56) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_755])).

tff(c_800,plain,(
    ! [A_17,C_56] :
      ( k1_setfam_1(k2_tarski(A_17,C_56)) = k3_xboole_0(A_17,C_56)
      | k1_tarski(C_56) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_785])).

tff(c_801,plain,(
    ! [A_17,C_56] : k1_setfam_1(k2_tarski(A_17,C_56)) = k3_xboole_0(A_17,C_56) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_800])).

tff(c_28,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_28])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.32  
% 2.50/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.32  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.50/1.32  
% 2.50/1.32  %Foreground sorts:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Background operators:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Foreground operators:
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.32  
% 2.50/1.33  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.50/1.33  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.50/1.33  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.50/1.33  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.50/1.33  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.50/1.33  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.50/1.33  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.50/1.33  tff(c_10, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.33  tff(c_12, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.33  tff(c_100, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k2_tarski(A_54, B_55), k1_tarski(C_56))=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.33  tff(c_109, plain, (![A_17, C_56]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_56))=k1_enumset1(A_17, A_17, C_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 2.50/1.33  tff(c_113, plain, (![A_57, C_58]: (k2_xboole_0(k1_tarski(A_57), k1_tarski(C_58))=k2_tarski(A_57, C_58))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109])).
% 2.50/1.33  tff(c_22, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.33  tff(c_134, plain, (![A_59, C_60]: (k2_tarski(A_59, C_60)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_22])).
% 2.50/1.33  tff(c_136, plain, (![A_17]: (k1_tarski(A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_134])).
% 2.50/1.33  tff(c_26, plain, (![A_40]: (k1_setfam_1(k1_tarski(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.50/1.33  tff(c_112, plain, (![A_17, C_56]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_56))=k2_tarski(A_17, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109])).
% 2.50/1.33  tff(c_368, plain, (![A_94, B_95]: (k3_xboole_0(k1_setfam_1(A_94), k1_setfam_1(B_95))=k1_setfam_1(k2_xboole_0(A_94, B_95)) | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.50/1.33  tff(c_377, plain, (![A_40, B_95]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_40), B_95))=k3_xboole_0(A_40, k1_setfam_1(B_95)) | k1_xboole_0=B_95 | k1_tarski(A_40)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_368])).
% 2.50/1.33  tff(c_755, plain, (![A_128, B_129]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_128), B_129))=k3_xboole_0(A_128, k1_setfam_1(B_129)) | k1_xboole_0=B_129)), inference(negUnitSimplification, [status(thm)], [c_136, c_377])).
% 2.50/1.33  tff(c_785, plain, (![A_17, C_56]: (k3_xboole_0(A_17, k1_setfam_1(k1_tarski(C_56)))=k1_setfam_1(k2_tarski(A_17, C_56)) | k1_tarski(C_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_755])).
% 2.50/1.33  tff(c_800, plain, (![A_17, C_56]: (k1_setfam_1(k2_tarski(A_17, C_56))=k3_xboole_0(A_17, C_56) | k1_tarski(C_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_785])).
% 2.50/1.33  tff(c_801, plain, (![A_17, C_56]: (k1_setfam_1(k2_tarski(A_17, C_56))=k3_xboole_0(A_17, C_56))), inference(negUnitSimplification, [status(thm)], [c_136, c_800])).
% 2.50/1.33  tff(c_28, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.50/1.33  tff(c_824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_801, c_28])).
% 2.50/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  Inference rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Ref     : 0
% 2.50/1.33  #Sup     : 186
% 2.50/1.33  #Fact    : 0
% 2.50/1.33  #Define  : 0
% 2.50/1.33  #Split   : 0
% 2.50/1.33  #Chain   : 0
% 2.50/1.33  #Close   : 0
% 2.50/1.33  
% 2.50/1.33  Ordering : KBO
% 2.50/1.33  
% 2.50/1.33  Simplification rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Subsume      : 16
% 2.50/1.33  #Demod        : 139
% 2.50/1.33  #Tautology    : 128
% 2.50/1.33  #SimpNegUnit  : 11
% 2.50/1.33  #BackRed      : 3
% 2.50/1.33  
% 2.50/1.33  #Partial instantiations: 0
% 2.50/1.33  #Strategies tried      : 1
% 2.50/1.33  
% 2.50/1.33  Timing (in seconds)
% 2.50/1.33  ----------------------
% 2.50/1.34  Preprocessing        : 0.29
% 2.50/1.34  Parsing              : 0.16
% 2.50/1.34  CNF conversion       : 0.02
% 2.50/1.34  Main loop            : 0.29
% 2.50/1.34  Inferencing          : 0.12
% 2.50/1.34  Reduction            : 0.11
% 2.50/1.34  Demodulation         : 0.08
% 2.50/1.34  BG Simplification    : 0.02
% 2.50/1.34  Subsumption          : 0.03
% 2.50/1.34  Abstraction          : 0.02
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.60
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
