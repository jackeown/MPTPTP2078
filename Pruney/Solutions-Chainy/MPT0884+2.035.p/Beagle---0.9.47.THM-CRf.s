%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 23.07s
% Output     : CNFRefutation 23.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
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

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_210,plain,(
    ! [A_77,B_78,C_79] : k2_zfmisc_1(k2_tarski(A_77,B_78),k1_tarski(C_79)) = k2_tarski(k4_tarski(A_77,C_79),k4_tarski(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_43,B_44,C_45] : k2_zfmisc_1(k2_zfmisc_1(A_43,B_44),C_45) = k3_zfmisc_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_225,plain,(
    ! [A_77,C_79,B_78,C_45] : k2_zfmisc_1(k2_tarski(k4_tarski(A_77,C_79),k4_tarski(B_78,C_79)),C_45) = k3_zfmisc_1(k2_tarski(A_77,B_78),k1_tarski(C_79),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_26])).

tff(c_24,plain,(
    ! [A_40,B_41,C_42] : k4_tarski(k4_tarski(A_40,B_41),C_42) = k3_mcart_1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_569,plain,(
    ! [A_118,C_119,D_120,B_121] : k2_enumset1(k4_tarski(A_118,C_119),k4_tarski(A_118,D_120),k4_tarski(B_121,C_119),k4_tarski(B_121,D_120)) = k2_zfmisc_1(k2_tarski(A_118,B_121),k2_tarski(C_119,D_120)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_602,plain,(
    ! [C_42,B_121,D_120,A_40,B_41] : k2_enumset1(k3_mcart_1(A_40,B_41,C_42),k4_tarski(k4_tarski(A_40,B_41),D_120),k4_tarski(B_121,C_42),k4_tarski(B_121,D_120)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_40,B_41),B_121),k2_tarski(C_42,D_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_569])).

tff(c_4101,plain,(
    ! [D_260,B_262,C_261,A_259,B_263] : k2_enumset1(k3_mcart_1(A_259,B_263,C_261),k3_mcart_1(A_259,B_263,D_260),k4_tarski(B_262,C_261),k4_tarski(B_262,D_260)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_259,B_263),B_262),k2_tarski(C_261,D_260)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_602])).

tff(c_4132,plain,(
    ! [C_42,D_260,A_40,A_259,B_41,B_263] : k2_enumset1(k3_mcart_1(A_259,B_263,C_42),k3_mcart_1(A_259,B_263,D_260),k3_mcart_1(A_40,B_41,C_42),k4_tarski(k4_tarski(A_40,B_41),D_260)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_259,B_263),k4_tarski(A_40,B_41)),k2_tarski(C_42,D_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4101])).

tff(c_4145,plain,(
    ! [C_42,D_260,A_40,A_259,B_41,B_263] : k2_enumset1(k3_mcart_1(A_259,B_263,C_42),k3_mcart_1(A_259,B_263,D_260),k3_mcart_1(A_40,B_41,C_42),k3_mcart_1(A_40,B_41,D_260)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_259,B_263),k4_tarski(A_40,B_41)),k2_tarski(C_42,D_260)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4132])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] : k2_enumset1(A_1,C_3,B_2,D_4) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_35367,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4145,c_29])).

tff(c_35370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_35367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:25:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.07/13.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.07/13.64  
% 23.07/13.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.07/13.64  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 23.07/13.64  
% 23.07/13.64  %Foreground sorts:
% 23.07/13.64  
% 23.07/13.64  
% 23.07/13.64  %Background operators:
% 23.07/13.64  
% 23.07/13.64  
% 23.07/13.64  %Foreground operators:
% 23.07/13.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.07/13.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.07/13.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.07/13.64  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 23.07/13.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.07/13.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.07/13.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.07/13.64  tff('#skF_5', type, '#skF_5': $i).
% 23.07/13.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.07/13.64  tff('#skF_2', type, '#skF_2': $i).
% 23.07/13.64  tff('#skF_3', type, '#skF_3': $i).
% 23.07/13.64  tff('#skF_1', type, '#skF_1': $i).
% 23.07/13.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.07/13.64  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 23.07/13.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.07/13.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.07/13.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.07/13.64  tff('#skF_4', type, '#skF_4': $i).
% 23.07/13.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.07/13.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.07/13.64  
% 23.07/13.65  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 23.07/13.65  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 23.07/13.65  tff(f_49, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 23.07/13.65  tff(f_43, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 23.07/13.65  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 23.07/13.65  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 23.07/13.65  tff(c_210, plain, (![A_77, B_78, C_79]: (k2_zfmisc_1(k2_tarski(A_77, B_78), k1_tarski(C_79))=k2_tarski(k4_tarski(A_77, C_79), k4_tarski(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.07/13.65  tff(c_26, plain, (![A_43, B_44, C_45]: (k2_zfmisc_1(k2_zfmisc_1(A_43, B_44), C_45)=k3_zfmisc_1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.07/13.65  tff(c_225, plain, (![A_77, C_79, B_78, C_45]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_77, C_79), k4_tarski(B_78, C_79)), C_45)=k3_zfmisc_1(k2_tarski(A_77, B_78), k1_tarski(C_79), C_45))), inference(superposition, [status(thm), theory('equality')], [c_210, c_26])).
% 23.07/13.65  tff(c_24, plain, (![A_40, B_41, C_42]: (k4_tarski(k4_tarski(A_40, B_41), C_42)=k3_mcart_1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.07/13.65  tff(c_569, plain, (![A_118, C_119, D_120, B_121]: (k2_enumset1(k4_tarski(A_118, C_119), k4_tarski(A_118, D_120), k4_tarski(B_121, C_119), k4_tarski(B_121, D_120))=k2_zfmisc_1(k2_tarski(A_118, B_121), k2_tarski(C_119, D_120)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.07/13.65  tff(c_602, plain, (![C_42, B_121, D_120, A_40, B_41]: (k2_enumset1(k3_mcart_1(A_40, B_41, C_42), k4_tarski(k4_tarski(A_40, B_41), D_120), k4_tarski(B_121, C_42), k4_tarski(B_121, D_120))=k2_zfmisc_1(k2_tarski(k4_tarski(A_40, B_41), B_121), k2_tarski(C_42, D_120)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_569])).
% 23.07/13.65  tff(c_4101, plain, (![D_260, B_262, C_261, A_259, B_263]: (k2_enumset1(k3_mcart_1(A_259, B_263, C_261), k3_mcart_1(A_259, B_263, D_260), k4_tarski(B_262, C_261), k4_tarski(B_262, D_260))=k2_zfmisc_1(k2_tarski(k4_tarski(A_259, B_263), B_262), k2_tarski(C_261, D_260)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_602])).
% 23.07/13.65  tff(c_4132, plain, (![C_42, D_260, A_40, A_259, B_41, B_263]: (k2_enumset1(k3_mcart_1(A_259, B_263, C_42), k3_mcart_1(A_259, B_263, D_260), k3_mcart_1(A_40, B_41, C_42), k4_tarski(k4_tarski(A_40, B_41), D_260))=k2_zfmisc_1(k2_tarski(k4_tarski(A_259, B_263), k4_tarski(A_40, B_41)), k2_tarski(C_42, D_260)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4101])).
% 23.07/13.65  tff(c_4145, plain, (![C_42, D_260, A_40, A_259, B_41, B_263]: (k2_enumset1(k3_mcart_1(A_259, B_263, C_42), k3_mcart_1(A_259, B_263, D_260), k3_mcart_1(A_40, B_41, C_42), k3_mcart_1(A_40, B_41, D_260))=k2_zfmisc_1(k2_tarski(k4_tarski(A_259, B_263), k4_tarski(A_40, B_41)), k2_tarski(C_42, D_260)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4132])).
% 23.07/13.65  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (k2_enumset1(A_1, C_3, B_2, D_4)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.07/13.65  tff(c_28, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 23.07/13.65  tff(c_29, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 23.07/13.65  tff(c_35367, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4145, c_29])).
% 23.07/13.65  tff(c_35370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_35367])).
% 23.07/13.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.07/13.65  
% 23.07/13.65  Inference rules
% 23.07/13.65  ----------------------
% 23.07/13.65  #Ref     : 0
% 23.07/13.65  #Sup     : 8850
% 23.07/13.65  #Fact    : 0
% 23.07/13.65  #Define  : 0
% 23.07/13.65  #Split   : 0
% 23.07/13.65  #Chain   : 0
% 23.07/13.65  #Close   : 0
% 23.07/13.65  
% 23.07/13.65  Ordering : KBO
% 23.07/13.65  
% 23.07/13.65  Simplification rules
% 23.07/13.65  ----------------------
% 23.07/13.65  #Subsume      : 1013
% 23.07/13.65  #Demod        : 14639
% 23.07/13.65  #Tautology    : 2435
% 23.07/13.65  #SimpNegUnit  : 0
% 23.07/13.65  #BackRed      : 1
% 23.07/13.65  
% 23.07/13.65  #Partial instantiations: 0
% 23.07/13.65  #Strategies tried      : 1
% 23.07/13.65  
% 23.07/13.65  Timing (in seconds)
% 23.07/13.65  ----------------------
% 23.07/13.66  Preprocessing        : 0.30
% 23.07/13.66  Parsing              : 0.16
% 23.07/13.66  CNF conversion       : 0.02
% 23.07/13.66  Main loop            : 12.59
% 23.07/13.66  Inferencing          : 3.12
% 23.07/13.66  Reduction            : 7.52
% 23.07/13.66  Demodulation         : 6.94
% 23.07/13.66  BG Simplification    : 0.50
% 23.07/13.66  Subsumption          : 1.20
% 23.07/13.66  Abstraction          : 1.03
% 23.07/13.66  MUC search           : 0.00
% 23.07/13.66  Cooper               : 0.00
% 23.07/13.66  Total                : 12.92
% 23.07/13.66  Index Insertion      : 0.00
% 23.07/13.66  Index Deletion       : 0.00
% 23.07/13.66  Index Matching       : 0.00
% 23.07/13.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
