%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 16.91s
% Output     : CNFRefutation 17.06s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_668,plain,(
    ! [A_99,B_100,C_101] : k2_zfmisc_1(k2_tarski(A_99,B_100),k1_tarski(C_101)) = k2_tarski(k4_tarski(A_99,C_101),k4_tarski(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_43,B_44,C_45] : k2_zfmisc_1(k2_zfmisc_1(A_43,B_44),C_45) = k3_zfmisc_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_680,plain,(
    ! [A_99,C_101,B_100,C_45] : k2_zfmisc_1(k2_tarski(k4_tarski(A_99,C_101),k4_tarski(B_100,C_101)),C_45) = k3_zfmisc_1(k2_tarski(A_99,B_100),k1_tarski(C_101),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_26])).

tff(c_24,plain,(
    ! [A_40,B_41,C_42] : k4_tarski(k4_tarski(A_40,B_41),C_42) = k3_mcart_1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1224,plain,(
    ! [A_128,C_129,D_130,B_131] : k2_enumset1(k4_tarski(A_128,C_129),k4_tarski(A_128,D_130),k4_tarski(B_131,C_129),k4_tarski(B_131,D_130)) = k2_zfmisc_1(k2_tarski(A_128,B_131),k2_tarski(C_129,D_130)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1335,plain,(
    ! [C_42,D_130,A_128,A_40,B_41] : k2_enumset1(k4_tarski(A_128,C_42),k4_tarski(A_128,D_130),k3_mcart_1(A_40,B_41,C_42),k4_tarski(k4_tarski(A_40,B_41),D_130)) = k2_zfmisc_1(k2_tarski(A_128,k4_tarski(A_40,B_41)),k2_tarski(C_42,D_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1224])).

tff(c_4770,plain,(
    ! [A_271,B_274,D_273,C_272,A_270] : k2_enumset1(k4_tarski(A_271,C_272),k4_tarski(A_271,D_273),k3_mcart_1(A_270,B_274,C_272),k3_mcart_1(A_270,B_274,D_273)) = k2_zfmisc_1(k2_tarski(A_271,k4_tarski(A_270,B_274)),k2_tarski(C_272,D_273)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1335])).

tff(c_4852,plain,(
    ! [C_42,B_274,A_40,C_272,B_41,A_270] : k2_enumset1(k4_tarski(k4_tarski(A_40,B_41),C_272),k3_mcart_1(A_40,B_41,C_42),k3_mcart_1(A_270,B_274,C_272),k3_mcart_1(A_270,B_274,C_42)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_40,B_41),k4_tarski(A_270,B_274)),k2_tarski(C_272,C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4770])).

tff(c_4862,plain,(
    ! [C_42,B_274,A_40,C_272,B_41,A_270] : k2_enumset1(k3_mcart_1(A_40,B_41,C_272),k3_mcart_1(A_40,B_41,C_42),k3_mcart_1(A_270,B_274,C_272),k3_mcart_1(A_270,B_274,C_42)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_40,B_41),k4_tarski(A_270,B_274)),k2_tarski(C_272,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4852])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_32,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_31])).

tff(c_26548,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4862,c_32])).

tff(c_26551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_26548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 11:09:53 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.91/9.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.01/9.17  
% 17.01/9.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.01/9.18  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.01/9.18  
% 17.01/9.18  %Foreground sorts:
% 17.01/9.18  
% 17.01/9.18  
% 17.01/9.18  %Background operators:
% 17.01/9.18  
% 17.01/9.18  
% 17.01/9.18  %Foreground operators:
% 17.01/9.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.01/9.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.01/9.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.01/9.18  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 17.01/9.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.01/9.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.01/9.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.01/9.18  tff('#skF_5', type, '#skF_5': $i).
% 17.01/9.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.01/9.18  tff('#skF_2', type, '#skF_2': $i).
% 17.01/9.18  tff('#skF_3', type, '#skF_3': $i).
% 17.01/9.18  tff('#skF_1', type, '#skF_1': $i).
% 17.01/9.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.01/9.18  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 17.01/9.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.01/9.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.01/9.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.01/9.18  tff('#skF_4', type, '#skF_4': $i).
% 17.01/9.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.01/9.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.01/9.18  
% 17.06/9.19  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 17.06/9.19  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 17.06/9.19  tff(f_49, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 17.06/9.19  tff(f_53, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_mcart_1)).
% 17.06/9.19  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 17.06/9.19  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 17.06/9.19  tff(f_56, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 17.06/9.19  tff(c_668, plain, (![A_99, B_100, C_101]: (k2_zfmisc_1(k2_tarski(A_99, B_100), k1_tarski(C_101))=k2_tarski(k4_tarski(A_99, C_101), k4_tarski(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.06/9.19  tff(c_26, plain, (![A_43, B_44, C_45]: (k2_zfmisc_1(k2_zfmisc_1(A_43, B_44), C_45)=k3_zfmisc_1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.06/9.19  tff(c_680, plain, (![A_99, C_101, B_100, C_45]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_99, C_101), k4_tarski(B_100, C_101)), C_45)=k3_zfmisc_1(k2_tarski(A_99, B_100), k1_tarski(C_101), C_45))), inference(superposition, [status(thm), theory('equality')], [c_668, c_26])).
% 17.06/9.19  tff(c_24, plain, (![A_40, B_41, C_42]: (k4_tarski(k4_tarski(A_40, B_41), C_42)=k3_mcart_1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.06/9.19  tff(c_1224, plain, (![A_128, C_129, D_130, B_131]: (k2_enumset1(k4_tarski(A_128, C_129), k4_tarski(A_128, D_130), k4_tarski(B_131, C_129), k4_tarski(B_131, D_130))=k2_zfmisc_1(k2_tarski(A_128, B_131), k2_tarski(C_129, D_130)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.06/9.19  tff(c_1335, plain, (![C_42, D_130, A_128, A_40, B_41]: (k2_enumset1(k4_tarski(A_128, C_42), k4_tarski(A_128, D_130), k3_mcart_1(A_40, B_41, C_42), k4_tarski(k4_tarski(A_40, B_41), D_130))=k2_zfmisc_1(k2_tarski(A_128, k4_tarski(A_40, B_41)), k2_tarski(C_42, D_130)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1224])).
% 17.06/9.19  tff(c_4770, plain, (![A_271, B_274, D_273, C_272, A_270]: (k2_enumset1(k4_tarski(A_271, C_272), k4_tarski(A_271, D_273), k3_mcart_1(A_270, B_274, C_272), k3_mcart_1(A_270, B_274, D_273))=k2_zfmisc_1(k2_tarski(A_271, k4_tarski(A_270, B_274)), k2_tarski(C_272, D_273)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1335])).
% 17.06/9.19  tff(c_4852, plain, (![C_42, B_274, A_40, C_272, B_41, A_270]: (k2_enumset1(k4_tarski(k4_tarski(A_40, B_41), C_272), k3_mcart_1(A_40, B_41, C_42), k3_mcart_1(A_270, B_274, C_272), k3_mcart_1(A_270, B_274, C_42))=k2_zfmisc_1(k2_tarski(k4_tarski(A_40, B_41), k4_tarski(A_270, B_274)), k2_tarski(C_272, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4770])).
% 17.06/9.19  tff(c_4862, plain, (![C_42, B_274, A_40, C_272, B_41, A_270]: (k2_enumset1(k3_mcart_1(A_40, B_41, C_272), k3_mcart_1(A_40, B_41, C_42), k3_mcart_1(A_270, B_274, C_272), k3_mcart_1(A_270, B_274, C_42))=k2_zfmisc_1(k2_tarski(k4_tarski(A_40, B_41), k4_tarski(A_270, B_274)), k2_tarski(C_272, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4852])).
% 17.06/9.19  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.06/9.19  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.06/9.19  tff(c_30, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.06/9.19  tff(c_31, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_30])).
% 17.06/9.19  tff(c_32, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_31])).
% 17.06/9.19  tff(c_26548, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4862, c_32])).
% 17.06/9.19  tff(c_26551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_680, c_26548])).
% 17.06/9.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.06/9.19  
% 17.06/9.19  Inference rules
% 17.06/9.19  ----------------------
% 17.06/9.19  #Ref     : 0
% 17.06/9.19  #Sup     : 6609
% 17.06/9.19  #Fact    : 0
% 17.06/9.19  #Define  : 0
% 17.06/9.19  #Split   : 0
% 17.06/9.19  #Chain   : 0
% 17.06/9.19  #Close   : 0
% 17.06/9.19  
% 17.06/9.19  Ordering : KBO
% 17.06/9.19  
% 17.06/9.19  Simplification rules
% 17.06/9.19  ----------------------
% 17.06/9.19  #Subsume      : 747
% 17.06/9.19  #Demod        : 10729
% 17.06/9.19  #Tautology    : 2285
% 17.06/9.19  #SimpNegUnit  : 0
% 17.06/9.19  #BackRed      : 1
% 17.06/9.19  
% 17.06/9.19  #Partial instantiations: 0
% 17.06/9.19  #Strategies tried      : 1
% 17.06/9.19  
% 17.06/9.19  Timing (in seconds)
% 17.06/9.19  ----------------------
% 17.06/9.19  Preprocessing        : 0.32
% 17.06/9.19  Parsing              : 0.18
% 17.06/9.19  CNF conversion       : 0.02
% 17.06/9.19  Main loop            : 8.13
% 17.06/9.19  Inferencing          : 2.16
% 17.06/9.19  Reduction            : 4.64
% 17.06/9.19  Demodulation         : 4.24
% 17.06/9.19  BG Simplification    : 0.34
% 17.06/9.19  Subsumption          : 0.79
% 17.06/9.19  Abstraction          : 0.68
% 17.06/9.19  MUC search           : 0.00
% 17.06/9.19  Cooper               : 0.00
% 17.06/9.19  Total                : 8.48
% 17.06/9.19  Index Insertion      : 0.00
% 17.06/9.19  Index Deletion       : 0.00
% 17.06/9.19  Index Matching       : 0.00
% 17.06/9.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
