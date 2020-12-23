%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:01 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   49 (  49 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_192,plain,(
    ! [C_65,B_66,A_67] : k1_enumset1(C_65,B_66,A_67) = k1_enumset1(A_67,B_66,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [C_65,B_66] : k1_enumset1(C_65,B_66,B_66) = k2_tarski(B_66,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_16])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_315,plain,(
    ! [B_88,D_91,F_92,C_93,E_89,A_90] : k2_xboole_0(k1_tarski(A_90),k3_enumset1(B_88,C_93,D_91,E_89,F_92)) = k4_enumset1(A_90,B_88,C_93,D_91,E_89,F_92) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),B_47) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_341,plain,(
    ! [F_102,C_104,A_106,B_105,D_101,E_103] : k4_enumset1(A_106,B_105,C_104,D_101,E_103,F_102) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_30])).

tff(c_344,plain,(
    ! [C_110,E_111,A_109,B_108,D_107] : k3_enumset1(A_109,B_108,C_110,D_107,E_111) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_341])).

tff(c_347,plain,(
    ! [A_112,B_113,C_114,D_115] : k2_enumset1(A_112,B_113,C_114,D_115) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_344])).

tff(c_350,plain,(
    ! [A_116,B_117,C_118] : k1_enumset1(A_116,B_117,C_118) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_347])).

tff(c_352,plain,(
    ! [B_66,C_65] : k2_tarski(B_66,C_65) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_350])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(A_53,B_54)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_63])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:01:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.25  
% 2.16/1.26  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 2.16/1.26  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.16/1.26  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.16/1.26  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.16/1.26  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.16/1.26  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.16/1.26  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.16/1.26  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.16/1.26  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.16/1.26  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.16/1.26  tff(c_192, plain, (![C_65, B_66, A_67]: (k1_enumset1(C_65, B_66, A_67)=k1_enumset1(A_67, B_66, C_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.26  tff(c_16, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.26  tff(c_208, plain, (![C_65, B_66]: (k1_enumset1(C_65, B_66, B_66)=k2_tarski(B_66, C_65))), inference(superposition, [status(thm), theory('equality')], [c_192, c_16])).
% 2.16/1.26  tff(c_18, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.26  tff(c_20, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.26  tff(c_22, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.26  tff(c_315, plain, (![B_88, D_91, F_92, C_93, E_89, A_90]: (k2_xboole_0(k1_tarski(A_90), k3_enumset1(B_88, C_93, D_91, E_89, F_92))=k4_enumset1(A_90, B_88, C_93, D_91, E_89, F_92))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.26  tff(c_30, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.26  tff(c_341, plain, (![F_102, C_104, A_106, B_105, D_101, E_103]: (k4_enumset1(A_106, B_105, C_104, D_101, E_103, F_102)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_315, c_30])).
% 2.16/1.26  tff(c_344, plain, (![C_110, E_111, A_109, B_108, D_107]: (k3_enumset1(A_109, B_108, C_110, D_107, E_111)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_341])).
% 2.16/1.26  tff(c_347, plain, (![A_112, B_113, C_114, D_115]: (k2_enumset1(A_112, B_113, C_114, D_115)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_344])).
% 2.16/1.26  tff(c_350, plain, (![A_116, B_117, C_118]: (k1_enumset1(A_116, B_117, C_118)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_347])).
% 2.16/1.26  tff(c_352, plain, (![B_66, C_65]: (k2_tarski(B_66, C_65)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_208, c_350])).
% 2.16/1.26  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.26  tff(c_63, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(A_53, B_54))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.26  tff(c_70, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32, c_63])).
% 2.16/1.26  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.26  tff(c_76, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 2.16/1.26  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_76])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 87
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 0
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 2
% 2.16/1.26  #Demod        : 18
% 2.16/1.26  #Tautology    : 69
% 2.16/1.26  #SimpNegUnit  : 1
% 2.16/1.26  #BackRed      : 3
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.30
% 2.16/1.26  Parsing              : 0.16
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.19
% 2.16/1.26  Inferencing          : 0.08
% 2.16/1.26  Reduction            : 0.07
% 2.16/1.26  Demodulation         : 0.05
% 2.16/1.26  BG Simplification    : 0.01
% 2.16/1.26  Subsumption          : 0.02
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.52
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
