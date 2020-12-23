%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  72 expanded)
%              Number of equality atoms :   33 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_87,plain,(
    ! [A_53,B_54,C_55] : k2_enumset1(A_53,A_53,B_54,C_55) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_29,B_30] : k2_enumset1(A_29,A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [B_54,C_55] : k1_enumset1(B_54,B_54,C_55) = k2_tarski(B_54,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_16])).

tff(c_8,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1133,plain,(
    ! [A_105,B_106,C_107,D_108] : k2_xboole_0(k1_enumset1(A_105,B_106,C_107),k1_tarski(D_108)) = k2_enumset1(A_105,B_106,C_107,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1142,plain,(
    ! [B_54,C_55,D_108] : k2_xboole_0(k2_tarski(B_54,C_55),k1_tarski(D_108)) = k2_enumset1(B_54,B_54,C_55,D_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1133])).

tff(c_1514,plain,(
    ! [B_116,C_117,D_118] : k2_xboole_0(k2_tarski(B_116,C_117),k1_tarski(D_118)) = k1_enumset1(B_116,C_117,D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1142])).

tff(c_1523,plain,(
    ! [A_14,D_118] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_118)) = k1_enumset1(A_14,A_14,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1514])).

tff(c_1526,plain,(
    ! [A_14,D_118] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_118)) = k2_tarski(A_14,D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1523])).

tff(c_973,plain,(
    ! [A_88,B_89,C_90,D_91] : k2_xboole_0(k1_enumset1(A_88,B_89,C_90),k1_tarski(D_91)) = k2_enumset1(A_88,B_89,C_90,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_982,plain,(
    ! [B_54,C_55,D_91] : k2_xboole_0(k2_tarski(B_54,C_55),k1_tarski(D_91)) = k2_enumset1(B_54,B_54,C_55,D_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_973])).

tff(c_986,plain,(
    ! [B_92,C_93,D_94] : k2_xboole_0(k2_tarski(B_92,C_93),k1_tarski(D_94)) = k1_enumset1(B_92,C_93,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_982])).

tff(c_995,plain,(
    ! [A_14,D_94] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_94)) = k1_enumset1(A_14,A_14,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_986])).

tff(c_998,plain,(
    ! [A_14,D_94] : k2_xboole_0(k1_tarski(A_14),k1_tarski(D_94)) = k2_tarski(A_14,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_995])).

tff(c_24,plain,(
    ! [A_42,C_44,B_43] : k2_xboole_0(k2_zfmisc_1(A_42,C_44),k2_zfmisc_1(B_43,C_44)) = k2_zfmisc_1(k2_xboole_0(A_42,B_43),C_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [C_44,A_42,B_43] : k2_xboole_0(k2_zfmisc_1(C_44,A_42),k2_zfmisc_1(C_44,B_43)) = k2_zfmisc_1(C_44,k2_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_30,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_29])).

tff(c_122,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_122])).

tff(c_1002,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_1002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  
% 3.52/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.57  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.52/1.57  
% 3.52/1.57  %Foreground sorts:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Background operators:
% 3.52/1.57  
% 3.52/1.57  
% 3.52/1.57  %Foreground operators:
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.52/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.57  
% 3.52/1.58  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.52/1.58  tff(f_41, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 3.52/1.58  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.52/1.58  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.52/1.58  tff(f_51, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 3.52/1.58  tff(f_56, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 3.52/1.58  tff(c_87, plain, (![A_53, B_54, C_55]: (k2_enumset1(A_53, A_53, B_54, C_55)=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.58  tff(c_16, plain, (![A_29, B_30]: (k2_enumset1(A_29, A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.58  tff(c_94, plain, (![B_54, C_55]: (k1_enumset1(B_54, B_54, C_55)=k2_tarski(B_54, C_55))), inference(superposition, [status(thm), theory('equality')], [c_87, c_16])).
% 3.52/1.58  tff(c_8, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.52/1.58  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.58  tff(c_1133, plain, (![A_105, B_106, C_107, D_108]: (k2_xboole_0(k1_enumset1(A_105, B_106, C_107), k1_tarski(D_108))=k2_enumset1(A_105, B_106, C_107, D_108))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.58  tff(c_1142, plain, (![B_54, C_55, D_108]: (k2_xboole_0(k2_tarski(B_54, C_55), k1_tarski(D_108))=k2_enumset1(B_54, B_54, C_55, D_108))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1133])).
% 3.52/1.58  tff(c_1514, plain, (![B_116, C_117, D_118]: (k2_xboole_0(k2_tarski(B_116, C_117), k1_tarski(D_118))=k1_enumset1(B_116, C_117, D_118))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1142])).
% 3.52/1.58  tff(c_1523, plain, (![A_14, D_118]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_118))=k1_enumset1(A_14, A_14, D_118))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1514])).
% 3.52/1.58  tff(c_1526, plain, (![A_14, D_118]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_118))=k2_tarski(A_14, D_118))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1523])).
% 3.52/1.58  tff(c_973, plain, (![A_88, B_89, C_90, D_91]: (k2_xboole_0(k1_enumset1(A_88, B_89, C_90), k1_tarski(D_91))=k2_enumset1(A_88, B_89, C_90, D_91))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.58  tff(c_982, plain, (![B_54, C_55, D_91]: (k2_xboole_0(k2_tarski(B_54, C_55), k1_tarski(D_91))=k2_enumset1(B_54, B_54, C_55, D_91))), inference(superposition, [status(thm), theory('equality')], [c_94, c_973])).
% 3.52/1.58  tff(c_986, plain, (![B_92, C_93, D_94]: (k2_xboole_0(k2_tarski(B_92, C_93), k1_tarski(D_94))=k1_enumset1(B_92, C_93, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_982])).
% 3.52/1.58  tff(c_995, plain, (![A_14, D_94]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_94))=k1_enumset1(A_14, A_14, D_94))), inference(superposition, [status(thm), theory('equality')], [c_8, c_986])).
% 3.52/1.58  tff(c_998, plain, (![A_14, D_94]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(D_94))=k2_tarski(A_14, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_995])).
% 3.52/1.58  tff(c_24, plain, (![A_42, C_44, B_43]: (k2_xboole_0(k2_zfmisc_1(A_42, C_44), k2_zfmisc_1(B_43, C_44))=k2_zfmisc_1(k2_xboole_0(A_42, B_43), C_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.58  tff(c_26, plain, (![C_44, A_42, B_43]: (k2_xboole_0(k2_zfmisc_1(C_44, A_42), k2_zfmisc_1(C_44, B_43))=k2_zfmisc_1(C_44, k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.58  tff(c_28, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.58  tff(c_29, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.52/1.58  tff(c_30, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_29])).
% 3.52/1.58  tff(c_122, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.52/1.58  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_998, c_122])).
% 3.52/1.58  tff(c_1002, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 3.52/1.58  tff(c_1532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1526, c_1002])).
% 3.52/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  Inference rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Ref     : 0
% 3.52/1.59  #Sup     : 384
% 3.52/1.59  #Fact    : 0
% 3.52/1.59  #Define  : 0
% 3.52/1.59  #Split   : 1
% 3.52/1.59  #Chain   : 0
% 3.52/1.59  #Close   : 0
% 3.52/1.59  
% 3.52/1.59  Ordering : KBO
% 3.52/1.59  
% 3.52/1.59  Simplification rules
% 3.52/1.59  ----------------------
% 3.52/1.59  #Subsume      : 34
% 3.52/1.59  #Demod        : 193
% 3.52/1.59  #Tautology    : 103
% 3.52/1.59  #SimpNegUnit  : 0
% 3.52/1.59  #BackRed      : 3
% 3.52/1.59  
% 3.52/1.59  #Partial instantiations: 0
% 3.52/1.59  #Strategies tried      : 1
% 3.52/1.59  
% 3.52/1.59  Timing (in seconds)
% 3.52/1.59  ----------------------
% 3.52/1.59  Preprocessing        : 0.31
% 3.52/1.59  Parsing              : 0.17
% 3.52/1.59  CNF conversion       : 0.02
% 3.52/1.59  Main loop            : 0.52
% 3.52/1.59  Inferencing          : 0.17
% 3.52/1.59  Reduction            : 0.23
% 3.52/1.59  Demodulation         : 0.20
% 3.52/1.59  BG Simplification    : 0.03
% 3.52/1.59  Subsumption          : 0.06
% 3.52/1.59  Abstraction          : 0.04
% 3.52/1.59  MUC search           : 0.00
% 3.52/1.59  Cooper               : 0.00
% 3.52/1.59  Total                : 0.86
% 3.52/1.59  Index Insertion      : 0.00
% 3.52/1.59  Index Deletion       : 0.00
% 3.52/1.59  Index Matching       : 0.00
% 3.52/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
