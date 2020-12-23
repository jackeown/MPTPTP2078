%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 25.17s
% Output     : CNFRefutation 25.17s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_622,plain,(
    ! [A_78,B_79,C_80] : k2_zfmisc_1(k2_tarski(A_78,B_79),k1_tarski(C_80)) = k2_tarski(k4_tarski(A_78,C_80),k4_tarski(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_641,plain,(
    ! [A_78,C_80,B_79,C_31] : k2_zfmisc_1(k2_tarski(k4_tarski(A_78,C_80),k4_tarski(B_79,C_80)),C_31) = k3_zfmisc_1(k2_tarski(A_78,B_79),k1_tarski(C_80),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_22])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] : k4_tarski(k4_tarski(A_26,B_27),C_28) = k3_mcart_1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_782,plain,(
    ! [A_84,C_85,D_86,B_87] : k2_enumset1(k4_tarski(A_84,C_85),k4_tarski(A_84,D_86),k4_tarski(B_87,C_85),k4_tarski(B_87,D_86)) = k2_zfmisc_1(k2_tarski(A_84,B_87),k2_tarski(C_85,D_86)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_862,plain,(
    ! [B_27,C_85,B_87,A_26,C_28] : k2_enumset1(k4_tarski(k4_tarski(A_26,B_27),C_85),k3_mcart_1(A_26,B_27,C_28),k4_tarski(B_87,C_85),k4_tarski(B_87,C_28)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_26,B_27),B_87),k2_tarski(C_85,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_782])).

tff(c_4489,plain,(
    ! [C_225,C_228,B_227,B_224,A_226] : k2_enumset1(k3_mcart_1(A_226,B_224,C_225),k3_mcart_1(A_226,B_224,C_228),k4_tarski(B_227,C_225),k4_tarski(B_227,C_228)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_226,B_224),B_227),k2_tarski(C_225,C_228)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_862])).

tff(c_4567,plain,(
    ! [B_27,C_225,A_26,B_224,A_226,C_28] : k2_enumset1(k3_mcart_1(A_226,B_224,C_225),k3_mcart_1(A_226,B_224,C_28),k4_tarski(k4_tarski(A_26,B_27),C_225),k3_mcart_1(A_26,B_27,C_28)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_226,B_224),k4_tarski(A_26,B_27)),k2_tarski(C_225,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4489])).

tff(c_4580,plain,(
    ! [B_27,C_225,A_26,B_224,A_226,C_28] : k2_enumset1(k3_mcart_1(A_226,B_224,C_225),k3_mcart_1(A_226,B_224,C_28),k3_mcart_1(A_26,B_27,C_225),k3_mcart_1(A_26,B_27,C_28)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_226,B_224),k4_tarski(A_26,B_27)),k2_tarski(C_225,C_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4567])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4,C_3] : k2_enumset1(A_1,B_2,D_4,C_3) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_26,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25])).

tff(c_30435,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4580,c_26])).

tff(c_30438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_30435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:43:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.17/14.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.17/14.65  
% 25.17/14.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.17/14.66  %$ k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.17/14.66  
% 25.17/14.66  %Foreground sorts:
% 25.17/14.66  
% 25.17/14.66  
% 25.17/14.66  %Background operators:
% 25.17/14.66  
% 25.17/14.66  
% 25.17/14.66  %Foreground operators:
% 25.17/14.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.17/14.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.17/14.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 25.17/14.66  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 25.17/14.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.17/14.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.17/14.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.17/14.66  tff('#skF_5', type, '#skF_5': $i).
% 25.17/14.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.17/14.66  tff('#skF_2', type, '#skF_2': $i).
% 25.17/14.66  tff('#skF_3', type, '#skF_3': $i).
% 25.17/14.66  tff('#skF_1', type, '#skF_1': $i).
% 25.17/14.66  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 25.17/14.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.17/14.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.17/14.66  tff('#skF_4', type, '#skF_4': $i).
% 25.17/14.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.17/14.66  
% 25.17/14.67  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 25.17/14.67  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 25.17/14.67  tff(f_45, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 25.17/14.67  tff(f_39, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 25.17/14.67  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 25.17/14.67  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 25.17/14.67  tff(f_50, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 25.17/14.67  tff(c_622, plain, (![A_78, B_79, C_80]: (k2_zfmisc_1(k2_tarski(A_78, B_79), k1_tarski(C_80))=k2_tarski(k4_tarski(A_78, C_80), k4_tarski(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 25.17/14.67  tff(c_22, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.17/14.67  tff(c_641, plain, (![A_78, C_80, B_79, C_31]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_78, C_80), k4_tarski(B_79, C_80)), C_31)=k3_zfmisc_1(k2_tarski(A_78, B_79), k1_tarski(C_80), C_31))), inference(superposition, [status(thm), theory('equality')], [c_622, c_22])).
% 25.17/14.67  tff(c_20, plain, (![A_26, B_27, C_28]: (k4_tarski(k4_tarski(A_26, B_27), C_28)=k3_mcart_1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.17/14.67  tff(c_782, plain, (![A_84, C_85, D_86, B_87]: (k2_enumset1(k4_tarski(A_84, C_85), k4_tarski(A_84, D_86), k4_tarski(B_87, C_85), k4_tarski(B_87, D_86))=k2_zfmisc_1(k2_tarski(A_84, B_87), k2_tarski(C_85, D_86)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.17/14.67  tff(c_862, plain, (![B_27, C_85, B_87, A_26, C_28]: (k2_enumset1(k4_tarski(k4_tarski(A_26, B_27), C_85), k3_mcart_1(A_26, B_27, C_28), k4_tarski(B_87, C_85), k4_tarski(B_87, C_28))=k2_zfmisc_1(k2_tarski(k4_tarski(A_26, B_27), B_87), k2_tarski(C_85, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_782])).
% 25.17/14.67  tff(c_4489, plain, (![C_225, C_228, B_227, B_224, A_226]: (k2_enumset1(k3_mcart_1(A_226, B_224, C_225), k3_mcart_1(A_226, B_224, C_228), k4_tarski(B_227, C_225), k4_tarski(B_227, C_228))=k2_zfmisc_1(k2_tarski(k4_tarski(A_226, B_224), B_227), k2_tarski(C_225, C_228)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_862])).
% 25.17/14.67  tff(c_4567, plain, (![B_27, C_225, A_26, B_224, A_226, C_28]: (k2_enumset1(k3_mcart_1(A_226, B_224, C_225), k3_mcart_1(A_226, B_224, C_28), k4_tarski(k4_tarski(A_26, B_27), C_225), k3_mcart_1(A_26, B_27, C_28))=k2_zfmisc_1(k2_tarski(k4_tarski(A_226, B_224), k4_tarski(A_26, B_27)), k2_tarski(C_225, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4489])).
% 25.17/14.67  tff(c_4580, plain, (![B_27, C_225, A_26, B_224, A_226, C_28]: (k2_enumset1(k3_mcart_1(A_226, B_224, C_225), k3_mcart_1(A_226, B_224, C_28), k3_mcart_1(A_26, B_27, C_225), k3_mcart_1(A_26, B_27, C_28))=k2_zfmisc_1(k2_tarski(k4_tarski(A_226, B_224), k4_tarski(A_26, B_27)), k2_tarski(C_225, C_28)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4567])).
% 25.17/14.67  tff(c_2, plain, (![A_1, B_2, D_4, C_3]: (k2_enumset1(A_1, B_2, D_4, C_3)=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.17/14.67  tff(c_4, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.17/14.67  tff(c_24, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 25.17/14.67  tff(c_25, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 25.17/14.67  tff(c_26, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_25])).
% 25.17/14.67  tff(c_30435, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4580, c_26])).
% 25.17/14.67  tff(c_30438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_30435])).
% 25.17/14.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.17/14.67  
% 25.17/14.67  Inference rules
% 25.17/14.67  ----------------------
% 25.17/14.67  #Ref     : 0
% 25.17/14.67  #Sup     : 7624
% 25.17/14.67  #Fact    : 0
% 25.17/14.67  #Define  : 0
% 25.17/14.67  #Split   : 0
% 25.17/14.67  #Chain   : 0
% 25.17/14.67  #Close   : 0
% 25.17/14.67  
% 25.17/14.67  Ordering : KBO
% 25.17/14.67  
% 25.17/14.67  Simplification rules
% 25.17/14.67  ----------------------
% 25.17/14.67  #Subsume      : 844
% 25.17/14.67  #Demod        : 12582
% 25.17/14.67  #Tautology    : 2509
% 25.17/14.67  #SimpNegUnit  : 0
% 25.17/14.67  #BackRed      : 1
% 25.17/14.67  
% 25.17/14.67  #Partial instantiations: 0
% 25.17/14.67  #Strategies tried      : 1
% 25.17/14.67  
% 25.17/14.67  Timing (in seconds)
% 25.17/14.67  ----------------------
% 25.17/14.67  Preprocessing        : 0.47
% 25.17/14.67  Parsing              : 0.24
% 25.17/14.67  CNF conversion       : 0.03
% 25.17/14.67  Main loop            : 13.27
% 25.17/14.67  Inferencing          : 3.38
% 25.17/14.67  Reduction            : 7.69
% 25.17/14.67  Demodulation         : 6.98
% 25.17/14.67  BG Simplification    : 0.57
% 25.17/14.67  Subsumption          : 1.30
% 25.17/14.67  Abstraction          : 1.15
% 25.17/14.67  MUC search           : 0.00
% 25.17/14.67  Cooper               : 0.00
% 25.17/14.67  Total                : 13.78
% 25.17/14.67  Index Insertion      : 0.00
% 25.17/14.67  Index Deletion       : 0.00
% 25.17/14.67  Index Matching       : 0.00
% 25.17/14.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
