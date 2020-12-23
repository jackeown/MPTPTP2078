%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:28 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   43 (  82 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   38 (  77 expanded)
%              Number of equality atoms :   37 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_6,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_31,B_32,C_33,D_34] : k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k1_tarski(D_34)) = k2_enumset1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_8,B_9,D_34] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(D_34)) = k2_enumset1(A_8,A_8,B_9,D_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_97,plain,(
    ! [A_35,B_36,D_37] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_37)) = k1_enumset1(A_35,B_36,D_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_93])).

tff(c_106,plain,(
    ! [A_7,D_37] : k2_xboole_0(k1_tarski(A_7),k1_tarski(D_37)) = k1_enumset1(A_7,A_7,D_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_110,plain,(
    ! [A_38,D_39] : k2_xboole_0(k1_tarski(A_38),k1_tarski(D_39)) = k2_tarski(A_38,D_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_12,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_40,D_41] : k2_tarski(A_40,D_41) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_123,plain,(
    ! [A_7] : k1_tarski(A_7) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_16,plain,(
    ! [A_17] : k1_setfam_1(k1_tarski(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,(
    ! [A_7,D_37] : k2_xboole_0(k1_tarski(A_7),k1_tarski(D_37)) = k2_tarski(A_7,D_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_158,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(k1_setfam_1(A_45),k1_setfam_1(B_46)) = k1_setfam_1(k2_xboole_0(A_45,B_46))
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_170,plain,(
    ! [A_17,B_46] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_17),B_46)) = k3_xboole_0(A_17,k1_setfam_1(B_46))
      | k1_xboole_0 = B_46
      | k1_tarski(A_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_178,plain,(
    ! [A_47,B_48] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_47),B_48)) = k3_xboole_0(A_47,k1_setfam_1(B_48))
      | k1_xboole_0 = B_48 ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_170])).

tff(c_193,plain,(
    ! [A_7,D_37] :
      ( k3_xboole_0(A_7,k1_setfam_1(k1_tarski(D_37))) = k1_setfam_1(k2_tarski(A_7,D_37))
      | k1_tarski(D_37) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_178])).

tff(c_198,plain,(
    ! [A_7,D_37] :
      ( k1_setfam_1(k2_tarski(A_7,D_37)) = k3_xboole_0(A_7,D_37)
      | k1_tarski(D_37) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_193])).

tff(c_199,plain,(
    ! [A_7,D_37] : k1_setfam_1(k2_tarski(A_7,D_37)) = k3_xboole_0(A_7,D_37) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_198])).

tff(c_18,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  %$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.73/1.15  
% 1.73/1.15  %Foreground sorts:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Background operators:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Foreground operators:
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.73/1.15  
% 1.73/1.16  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.73/1.16  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.73/1.16  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.73/1.16  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.73/1.16  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.73/1.16  tff(f_50, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.73/1.16  tff(f_48, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 1.73/1.16  tff(f_53, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.73/1.16  tff(c_6, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.16  tff(c_8, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.16  tff(c_10, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.16  tff(c_84, plain, (![A_31, B_32, C_33, D_34]: (k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k1_tarski(D_34))=k2_enumset1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.16  tff(c_93, plain, (![A_8, B_9, D_34]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(D_34))=k2_enumset1(A_8, A_8, B_9, D_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 1.73/1.16  tff(c_97, plain, (![A_35, B_36, D_37]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_37))=k1_enumset1(A_35, B_36, D_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_93])).
% 1.73/1.16  tff(c_106, plain, (![A_7, D_37]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(D_37))=k1_enumset1(A_7, A_7, D_37))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 1.73/1.16  tff(c_110, plain, (![A_38, D_39]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(D_39))=k2_tarski(A_38, D_39))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 1.73/1.16  tff(c_12, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.16  tff(c_121, plain, (![A_40, D_41]: (k2_tarski(A_40, D_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 1.73/1.16  tff(c_123, plain, (![A_7]: (k1_tarski(A_7)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 1.73/1.16  tff(c_16, plain, (![A_17]: (k1_setfam_1(k1_tarski(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.16  tff(c_109, plain, (![A_7, D_37]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(D_37))=k2_tarski(A_7, D_37))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 1.73/1.16  tff(c_158, plain, (![A_45, B_46]: (k3_xboole_0(k1_setfam_1(A_45), k1_setfam_1(B_46))=k1_setfam_1(k2_xboole_0(A_45, B_46)) | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.16  tff(c_170, plain, (![A_17, B_46]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_17), B_46))=k3_xboole_0(A_17, k1_setfam_1(B_46)) | k1_xboole_0=B_46 | k1_tarski(A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_158])).
% 1.73/1.16  tff(c_178, plain, (![A_47, B_48]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_47), B_48))=k3_xboole_0(A_47, k1_setfam_1(B_48)) | k1_xboole_0=B_48)), inference(negUnitSimplification, [status(thm)], [c_123, c_170])).
% 1.73/1.16  tff(c_193, plain, (![A_7, D_37]: (k3_xboole_0(A_7, k1_setfam_1(k1_tarski(D_37)))=k1_setfam_1(k2_tarski(A_7, D_37)) | k1_tarski(D_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_178])).
% 1.73/1.16  tff(c_198, plain, (![A_7, D_37]: (k1_setfam_1(k2_tarski(A_7, D_37))=k3_xboole_0(A_7, D_37) | k1_tarski(D_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_193])).
% 1.73/1.16  tff(c_199, plain, (![A_7, D_37]: (k1_setfam_1(k2_tarski(A_7, D_37))=k3_xboole_0(A_7, D_37))), inference(negUnitSimplification, [status(thm)], [c_123, c_198])).
% 1.73/1.16  tff(c_18, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.16  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_18])).
% 1.73/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  Inference rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Ref     : 0
% 1.73/1.16  #Sup     : 44
% 1.73/1.16  #Fact    : 0
% 1.73/1.16  #Define  : 0
% 1.73/1.16  #Split   : 0
% 1.73/1.16  #Chain   : 0
% 1.73/1.16  #Close   : 0
% 1.73/1.16  
% 1.73/1.16  Ordering : KBO
% 1.73/1.16  
% 1.73/1.16  Simplification rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Subsume      : 0
% 1.73/1.16  #Demod        : 7
% 1.73/1.16  #Tautology    : 27
% 1.73/1.16  #SimpNegUnit  : 5
% 1.73/1.16  #BackRed      : 1
% 1.73/1.16  
% 1.73/1.16  #Partial instantiations: 0
% 1.73/1.16  #Strategies tried      : 1
% 1.73/1.16  
% 1.73/1.16  Timing (in seconds)
% 1.73/1.16  ----------------------
% 1.73/1.17  Preprocessing        : 0.27
% 1.73/1.17  Parsing              : 0.15
% 1.73/1.17  CNF conversion       : 0.01
% 1.73/1.17  Main loop            : 0.14
% 1.73/1.17  Inferencing          : 0.06
% 1.73/1.17  Reduction            : 0.04
% 1.73/1.17  Demodulation         : 0.03
% 1.73/1.17  BG Simplification    : 0.01
% 1.73/1.17  Subsumption          : 0.02
% 1.73/1.17  Abstraction          : 0.01
% 1.73/1.17  MUC search           : 0.00
% 1.73/1.17  Cooper               : 0.00
% 1.73/1.17  Total                : 0.43
% 1.73/1.17  Index Insertion      : 0.00
% 1.73/1.17  Index Deletion       : 0.00
% 1.73/1.17  Index Matching       : 0.00
% 1.73/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
