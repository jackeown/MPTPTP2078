%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:27 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  53 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_18,plain,(
    ! [A_25] : k3_tarski(k1_tarski(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_17] : k3_tarski(k1_tarski(A_17)) = k2_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_77,plain,(
    ! [A_40] : k2_xboole_0(A_40,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_73])).

tff(c_20,plain,(
    ! [A_26,B_27] : k2_xboole_0(k1_tarski(A_26),B_27) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_84,plain,(
    ! [A_26] : k1_tarski(A_26) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_24,plain,(
    ! [A_30] : k1_setfam_1(k1_tarski(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(C_47)) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_17,C_47] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_47)) = k1_enumset1(A_17,A_17,C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_112,plain,(
    ! [A_17,C_47] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_47)) = k2_tarski(A_17,C_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_109])).

tff(c_227,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(k1_setfam_1(A_70),k1_setfam_1(B_71)) = k1_setfam_1(k2_xboole_0(A_70,B_71))
      | k1_xboole_0 = B_71
      | k1_xboole_0 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    ! [A_30,B_71] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_30),B_71)) = k3_xboole_0(A_30,k1_setfam_1(B_71))
      | k1_xboole_0 = B_71
      | k1_tarski(A_30) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_227])).

tff(c_620,plain,(
    ! [A_102,B_103] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_102),B_103)) = k3_xboole_0(A_102,k1_setfam_1(B_103))
      | k1_xboole_0 = B_103 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_236])).

tff(c_647,plain,(
    ! [A_17,C_47] :
      ( k3_xboole_0(A_17,k1_setfam_1(k1_tarski(C_47))) = k1_setfam_1(k2_tarski(A_17,C_47))
      | k1_tarski(C_47) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_620])).

tff(c_660,plain,(
    ! [A_17,C_47] :
      ( k1_setfam_1(k2_tarski(A_17,C_47)) = k3_xboole_0(A_17,C_47)
      | k1_tarski(C_47) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_647])).

tff(c_661,plain,(
    ! [A_17,C_47] : k1_setfam_1(k2_tarski(A_17,C_47)) = k3_xboole_0(A_17,C_47) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_660])).

tff(c_26,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.31  
% 2.43/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.31  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.43/1.31  
% 2.43/1.31  %Foreground sorts:
% 2.43/1.31  
% 2.43/1.31  
% 2.43/1.31  %Background operators:
% 2.43/1.31  
% 2.43/1.31  
% 2.43/1.31  %Foreground operators:
% 2.43/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.43/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.43/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.43/1.31  
% 2.43/1.32  tff(f_43, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.43/1.32  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.43/1.32  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.43/1.32  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.43/1.32  tff(f_58, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.43/1.32  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.43/1.32  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.43/1.32  tff(f_56, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.43/1.32  tff(f_61, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.43/1.32  tff(c_18, plain, (![A_25]: (k3_tarski(k1_tarski(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.32  tff(c_10, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.32  tff(c_64, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.32  tff(c_73, plain, (![A_17]: (k3_tarski(k1_tarski(A_17))=k2_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 2.43/1.32  tff(c_77, plain, (![A_40]: (k2_xboole_0(A_40, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_73])).
% 2.43/1.32  tff(c_20, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.32  tff(c_84, plain, (![A_26]: (k1_tarski(A_26)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77, c_20])).
% 2.43/1.32  tff(c_24, plain, (![A_30]: (k1_setfam_1(k1_tarski(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.32  tff(c_12, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.32  tff(c_100, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(C_47))=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.32  tff(c_109, plain, (![A_17, C_47]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_47))=k1_enumset1(A_17, A_17, C_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 2.43/1.32  tff(c_112, plain, (![A_17, C_47]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_47))=k2_tarski(A_17, C_47))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_109])).
% 2.43/1.32  tff(c_227, plain, (![A_70, B_71]: (k3_xboole_0(k1_setfam_1(A_70), k1_setfam_1(B_71))=k1_setfam_1(k2_xboole_0(A_70, B_71)) | k1_xboole_0=B_71 | k1_xboole_0=A_70)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.32  tff(c_236, plain, (![A_30, B_71]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_30), B_71))=k3_xboole_0(A_30, k1_setfam_1(B_71)) | k1_xboole_0=B_71 | k1_tarski(A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_227])).
% 2.43/1.32  tff(c_620, plain, (![A_102, B_103]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_102), B_103))=k3_xboole_0(A_102, k1_setfam_1(B_103)) | k1_xboole_0=B_103)), inference(negUnitSimplification, [status(thm)], [c_84, c_236])).
% 2.43/1.32  tff(c_647, plain, (![A_17, C_47]: (k3_xboole_0(A_17, k1_setfam_1(k1_tarski(C_47)))=k1_setfam_1(k2_tarski(A_17, C_47)) | k1_tarski(C_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_620])).
% 2.43/1.32  tff(c_660, plain, (![A_17, C_47]: (k1_setfam_1(k2_tarski(A_17, C_47))=k3_xboole_0(A_17, C_47) | k1_tarski(C_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_647])).
% 2.43/1.32  tff(c_661, plain, (![A_17, C_47]: (k1_setfam_1(k2_tarski(A_17, C_47))=k3_xboole_0(A_17, C_47))), inference(negUnitSimplification, [status(thm)], [c_84, c_660])).
% 2.43/1.32  tff(c_26, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.32  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_661, c_26])).
% 2.43/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  Inference rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Ref     : 0
% 2.43/1.32  #Sup     : 156
% 2.43/1.32  #Fact    : 0
% 2.43/1.32  #Define  : 0
% 2.43/1.32  #Split   : 0
% 2.43/1.32  #Chain   : 0
% 2.43/1.32  #Close   : 0
% 2.43/1.32  
% 2.43/1.32  Ordering : KBO
% 2.43/1.32  
% 2.43/1.32  Simplification rules
% 2.43/1.32  ----------------------
% 2.43/1.32  #Subsume      : 14
% 2.43/1.32  #Demod        : 109
% 2.43/1.32  #Tautology    : 109
% 2.43/1.32  #SimpNegUnit  : 10
% 2.43/1.32  #BackRed      : 2
% 2.43/1.32  
% 2.43/1.32  #Partial instantiations: 0
% 2.43/1.32  #Strategies tried      : 1
% 2.43/1.32  
% 2.43/1.32  Timing (in seconds)
% 2.43/1.32  ----------------------
% 2.43/1.33  Preprocessing        : 0.29
% 2.43/1.33  Parsing              : 0.16
% 2.43/1.33  CNF conversion       : 0.02
% 2.43/1.33  Main loop            : 0.26
% 2.43/1.33  Inferencing          : 0.11
% 2.43/1.33  Reduction            : 0.09
% 2.43/1.33  Demodulation         : 0.07
% 2.43/1.33  BG Simplification    : 0.02
% 2.43/1.33  Subsumption          : 0.03
% 2.43/1.33  Abstraction          : 0.02
% 2.43/1.33  MUC search           : 0.00
% 2.43/1.33  Cooper               : 0.00
% 2.43/1.33  Total                : 0.58
% 2.43/1.33  Index Insertion      : 0.00
% 2.43/1.33  Index Deletion       : 0.00
% 2.43/1.33  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
