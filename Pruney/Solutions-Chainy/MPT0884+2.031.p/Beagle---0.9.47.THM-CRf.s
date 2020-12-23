%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:35 EST 2020

% Result     : Theorem 38.87s
% Output     : CNFRefutation 38.87s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  46 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
      & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k4_tarski(k4_tarski(A_12,B_13),C_14) = k3_mcart_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_265,plain,(
    ! [A_50,B_51,C_52] : k2_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52)) = k2_tarski(k4_tarski(A_50,C_52),k4_tarski(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_299,plain,(
    ! [A_50,C_52,B_51,C_17] : k2_zfmisc_1(k2_tarski(k4_tarski(A_50,C_52),k4_tarski(B_51,C_52)),C_17) = k3_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52),C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2646,plain,(
    ! [C_161,C_159,D_158,A_157,B_160] : k2_xboole_0(k2_zfmisc_1(k2_tarski(A_157,B_160),k1_tarski(C_159)),k2_tarski(C_161,D_158)) = k2_enumset1(k4_tarski(A_157,C_159),k4_tarski(B_160,C_159),C_161,D_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_2759,plain,(
    ! [A_50,C_161,B_51,C_159,D_158,C_52] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52),k1_tarski(C_159)),k2_tarski(C_161,D_158)) = k2_enumset1(k4_tarski(k4_tarski(A_50,C_52),C_159),k4_tarski(k4_tarski(B_51,C_52),C_159),C_161,D_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_2646])).

tff(c_2843,plain,(
    ! [A_50,C_161,B_51,C_159,D_158,C_52] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52),k1_tarski(C_159)),k2_tarski(C_161,D_158)) = k2_enumset1(k3_mcart_1(A_50,C_52,C_159),k3_mcart_1(B_51,C_52,C_159),C_161,D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_2759])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k2_tarski(k4_tarski(A_9,C_11),k4_tarski(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_355,plain,(
    ! [C_56,A_57,B_58] : k2_xboole_0(k2_zfmisc_1(C_56,k1_tarski(A_57)),k2_zfmisc_1(C_56,k1_tarski(B_58))) = k2_zfmisc_1(C_56,k2_tarski(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5595,plain,(
    ! [A_244,B_245,A_246,C_247] : k2_xboole_0(k2_zfmisc_1(k2_tarski(A_244,B_245),k1_tarski(A_246)),k2_tarski(k4_tarski(A_244,C_247),k4_tarski(B_245,C_247))) = k2_zfmisc_1(k2_tarski(A_244,B_245),k2_tarski(A_246,C_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_355])).

tff(c_5678,plain,(
    ! [A_246,C_11,B_10,C_247,A_9] : k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(A_9,B_10),k1_tarski(C_11)),k1_tarski(A_246)),k2_tarski(k4_tarski(k4_tarski(A_9,C_11),C_247),k4_tarski(k4_tarski(B_10,C_11),C_247))) = k2_zfmisc_1(k2_tarski(k4_tarski(A_9,C_11),k4_tarski(B_10,C_11)),k2_tarski(A_246,C_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5595])).

tff(c_69165,plain,(
    ! [A_1196,C_1195,C_1192,A_1194,B_1193] : k2_xboole_0(k3_zfmisc_1(k2_tarski(A_1196,B_1193),k1_tarski(C_1195),k1_tarski(A_1194)),k2_tarski(k3_mcart_1(A_1196,C_1195,C_1192),k3_mcart_1(B_1193,C_1195,C_1192))) = k3_zfmisc_1(k2_tarski(A_1196,B_1193),k1_tarski(C_1195),k2_tarski(A_1194,C_1192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_14,c_14,c_16,c_5678])).

tff(c_69312,plain,(
    ! [A_50,B_51,C_159,C_1192,C_52] : k2_enumset1(k3_mcart_1(A_50,C_52,C_159),k3_mcart_1(B_51,C_52,C_159),k3_mcart_1(A_50,C_52,C_1192),k3_mcart_1(B_51,C_52,C_1192)) = k3_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52),k2_tarski(C_159,C_1192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_69165])).

tff(c_18,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69312,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.87/27.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.87/27.55  
% 38.87/27.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.87/27.55  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 38.87/27.55  
% 38.87/27.55  %Foreground sorts:
% 38.87/27.55  
% 38.87/27.55  
% 38.87/27.55  %Background operators:
% 38.87/27.55  
% 38.87/27.55  
% 38.87/27.55  %Foreground operators:
% 38.87/27.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.87/27.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 38.87/27.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 38.87/27.55  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 38.87/27.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 38.87/27.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 38.87/27.55  tff('#skF_5', type, '#skF_5': $i).
% 38.87/27.55  tff('#skF_2', type, '#skF_2': $i).
% 38.87/27.55  tff('#skF_3', type, '#skF_3': $i).
% 38.87/27.55  tff('#skF_1', type, '#skF_1': $i).
% 38.87/27.55  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 38.87/27.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.87/27.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 38.87/27.55  tff('#skF_4', type, '#skF_4': $i).
% 38.87/27.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.87/27.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 38.87/27.55  
% 38.87/27.57  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 38.87/27.57  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 38.87/27.57  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 38.87/27.57  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 38.87/27.57  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 38.87/27.57  tff(f_44, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 38.87/27.57  tff(c_14, plain, (![A_12, B_13, C_14]: (k4_tarski(k4_tarski(A_12, B_13), C_14)=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 38.87/27.57  tff(c_265, plain, (![A_50, B_51, C_52]: (k2_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52))=k2_tarski(k4_tarski(A_50, C_52), k4_tarski(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.87/27.57  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.87/27.57  tff(c_299, plain, (![A_50, C_52, B_51, C_17]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_50, C_52), k4_tarski(B_51, C_52)), C_17)=k3_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52), C_17))), inference(superposition, [status(thm), theory('equality')], [c_265, c_16])).
% 38.87/27.57  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.87/27.57  tff(c_2646, plain, (![C_161, C_159, D_158, A_157, B_160]: (k2_xboole_0(k2_zfmisc_1(k2_tarski(A_157, B_160), k1_tarski(C_159)), k2_tarski(C_161, D_158))=k2_enumset1(k4_tarski(A_157, C_159), k4_tarski(B_160, C_159), C_161, D_158))), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 38.87/27.57  tff(c_2759, plain, (![A_50, C_161, B_51, C_159, D_158, C_52]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52), k1_tarski(C_159)), k2_tarski(C_161, D_158))=k2_enumset1(k4_tarski(k4_tarski(A_50, C_52), C_159), k4_tarski(k4_tarski(B_51, C_52), C_159), C_161, D_158))), inference(superposition, [status(thm), theory('equality')], [c_299, c_2646])).
% 38.87/27.57  tff(c_2843, plain, (![A_50, C_161, B_51, C_159, D_158, C_52]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52), k1_tarski(C_159)), k2_tarski(C_161, D_158))=k2_enumset1(k3_mcart_1(A_50, C_52, C_159), k3_mcart_1(B_51, C_52, C_159), C_161, D_158))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_2759])).
% 38.87/27.57  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_tarski(A_9, B_10), k1_tarski(C_11))=k2_tarski(k4_tarski(A_9, C_11), k4_tarski(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.87/27.57  tff(c_355, plain, (![C_56, A_57, B_58]: (k2_xboole_0(k2_zfmisc_1(C_56, k1_tarski(A_57)), k2_zfmisc_1(C_56, k1_tarski(B_58)))=k2_zfmisc_1(C_56, k2_tarski(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 38.87/27.57  tff(c_5595, plain, (![A_244, B_245, A_246, C_247]: (k2_xboole_0(k2_zfmisc_1(k2_tarski(A_244, B_245), k1_tarski(A_246)), k2_tarski(k4_tarski(A_244, C_247), k4_tarski(B_245, C_247)))=k2_zfmisc_1(k2_tarski(A_244, B_245), k2_tarski(A_246, C_247)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_355])).
% 38.87/27.57  tff(c_5678, plain, (![A_246, C_11, B_10, C_247, A_9]: (k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(A_9, B_10), k1_tarski(C_11)), k1_tarski(A_246)), k2_tarski(k4_tarski(k4_tarski(A_9, C_11), C_247), k4_tarski(k4_tarski(B_10, C_11), C_247)))=k2_zfmisc_1(k2_tarski(k4_tarski(A_9, C_11), k4_tarski(B_10, C_11)), k2_tarski(A_246, C_247)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_5595])).
% 38.87/27.57  tff(c_69165, plain, (![A_1196, C_1195, C_1192, A_1194, B_1193]: (k2_xboole_0(k3_zfmisc_1(k2_tarski(A_1196, B_1193), k1_tarski(C_1195), k1_tarski(A_1194)), k2_tarski(k3_mcart_1(A_1196, C_1195, C_1192), k3_mcart_1(B_1193, C_1195, C_1192)))=k3_zfmisc_1(k2_tarski(A_1196, B_1193), k1_tarski(C_1195), k2_tarski(A_1194, C_1192)))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_14, c_14, c_16, c_5678])).
% 38.87/27.57  tff(c_69312, plain, (![A_50, B_51, C_159, C_1192, C_52]: (k2_enumset1(k3_mcart_1(A_50, C_52, C_159), k3_mcart_1(B_51, C_52, C_159), k3_mcart_1(A_50, C_52, C_1192), k3_mcart_1(B_51, C_52, C_1192))=k3_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52), k2_tarski(C_159, C_1192)))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_69165])).
% 38.87/27.57  tff(c_18, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 38.87/27.57  tff(c_70539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69312, c_18])).
% 38.87/27.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.87/27.57  
% 38.87/27.57  Inference rules
% 38.87/27.57  ----------------------
% 38.87/27.57  #Ref     : 0
% 38.87/27.57  #Sup     : 17486
% 38.87/27.57  #Fact    : 0
% 38.87/27.57  #Define  : 0
% 38.87/27.57  #Split   : 0
% 38.87/27.57  #Chain   : 0
% 38.87/27.57  #Close   : 0
% 38.87/27.57  
% 38.87/27.57  Ordering : KBO
% 38.87/27.57  
% 38.87/27.57  Simplification rules
% 38.87/27.57  ----------------------
% 38.87/27.57  #Subsume      : 2032
% 38.87/27.57  #Demod        : 28368
% 38.87/27.57  #Tautology    : 4405
% 38.87/27.57  #SimpNegUnit  : 0
% 38.87/27.57  #BackRed      : 1
% 38.87/27.57  
% 38.87/27.57  #Partial instantiations: 0
% 38.87/27.57  #Strategies tried      : 1
% 38.87/27.57  
% 38.87/27.57  Timing (in seconds)
% 38.87/27.57  ----------------------
% 38.87/27.57  Preprocessing        : 0.33
% 38.87/27.57  Parsing              : 0.19
% 38.87/27.57  CNF conversion       : 0.02
% 38.87/27.57  Main loop            : 26.46
% 38.87/27.57  Inferencing          : 5.40
% 38.87/27.57  Reduction            : 16.51
% 38.87/27.57  Demodulation         : 15.33
% 38.87/27.57  BG Simplification    : 0.98
% 38.87/27.57  Subsumption          : 2.98
% 38.87/27.57  Abstraction          : 1.95
% 38.87/27.57  MUC search           : 0.00
% 38.87/27.57  Cooper               : 0.00
% 38.87/27.57  Total                : 26.82
% 38.87/27.57  Index Insertion      : 0.00
% 38.87/27.57  Index Deletion       : 0.00
% 38.87/27.57  Index Matching       : 0.00
% 38.87/27.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
