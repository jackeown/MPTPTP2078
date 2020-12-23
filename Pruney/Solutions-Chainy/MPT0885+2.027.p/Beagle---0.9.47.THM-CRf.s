%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:38 EST 2020

% Result     : Theorem 41.74s
% Output     : CNFRefutation 41.74s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  48 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

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
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k1_tarski(A),k2_tarski(B,C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,B,D),k3_mcart_1(A,C,D),k3_mcart_1(A,B,E),k3_mcart_1(A,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k4_tarski(k4_tarski(A_12,B_13),C_14) = k3_mcart_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_32,B_33,C_34] : k2_zfmisc_1(k1_tarski(A_32),k2_tarski(B_33,C_34)) = k2_tarski(k4_tarski(A_32,B_33),k4_tarski(A_32,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_32,B_33,C_34,C_17] : k2_zfmisc_1(k2_tarski(k4_tarski(A_32,B_33),k4_tarski(A_32,C_34)),C_17) = k3_zfmisc_1(k1_tarski(A_32),k2_tarski(B_33,C_34),C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_16])).

tff(c_265,plain,(
    ! [A_50,B_51,C_52] : k2_zfmisc_1(k2_tarski(A_50,B_51),k1_tarski(C_52)) = k2_tarski(k4_tarski(A_50,C_52),k4_tarski(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2443,plain,(
    ! [A_152,B_155,A_156,C_153,B_154] : k2_xboole_0(k2_tarski(A_156,B_155),k2_zfmisc_1(k2_tarski(A_152,B_154),k1_tarski(C_153))) = k2_enumset1(A_156,B_155,k4_tarski(A_152,C_153),k4_tarski(B_154,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_2552,plain,(
    ! [B_155,B_33,A_156,C_34,C_153,A_32] : k2_xboole_0(k2_tarski(A_156,B_155),k3_zfmisc_1(k1_tarski(A_32),k2_tarski(B_33,C_34),k1_tarski(C_153))) = k2_enumset1(A_156,B_155,k4_tarski(k4_tarski(A_32,B_33),C_153),k4_tarski(k4_tarski(A_32,C_34),C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2443])).

tff(c_2633,plain,(
    ! [B_155,B_33,A_156,C_34,C_153,A_32] : k2_xboole_0(k2_tarski(A_156,B_155),k3_zfmisc_1(k1_tarski(A_32),k2_tarski(B_33,C_34),k1_tarski(C_153))) = k2_enumset1(A_156,B_155,k3_mcart_1(A_32,B_33,C_153),k3_mcart_1(A_32,C_34,C_153)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_2552])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k1_tarski(A_9),k2_tarski(B_10,C_11)) = k2_tarski(k4_tarski(A_9,B_10),k4_tarski(A_9,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_315,plain,(
    ! [A_9,B_10,C_11,C_52] : k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_9),k2_tarski(B_10,C_11)),k1_tarski(C_52)) = k2_tarski(k4_tarski(k4_tarski(A_9,B_10),C_52),k4_tarski(k4_tarski(A_9,C_11),C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_265])).

tff(c_1309,plain,(
    ! [A_114,B_115,C_116,C_117] : k3_zfmisc_1(k1_tarski(A_114),k2_tarski(B_115,C_116),k1_tarski(C_117)) = k2_tarski(k3_mcart_1(A_114,B_115,C_117),k3_mcart_1(A_114,C_116,C_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16,c_315])).

tff(c_355,plain,(
    ! [C_56,A_57,B_58] : k2_xboole_0(k2_zfmisc_1(C_56,k1_tarski(A_57)),k2_zfmisc_1(C_56,k1_tarski(B_58))) = k2_zfmisc_1(C_56,k2_tarski(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_381,plain,(
    ! [A_15,B_16,A_57,B_58] : k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),k1_tarski(A_57)),k3_zfmisc_1(A_15,B_16,k1_tarski(B_58))) = k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_355])).

tff(c_387,plain,(
    ! [A_15,B_16,A_57,B_58] : k2_xboole_0(k3_zfmisc_1(A_15,B_16,k1_tarski(A_57)),k3_zfmisc_1(A_15,B_16,k1_tarski(B_58))) = k3_zfmisc_1(A_15,B_16,k2_tarski(A_57,B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_381])).

tff(c_73702,plain,(
    ! [C_1258,C_1255,B_1257,B_1256,A_1259] : k2_xboole_0(k2_tarski(k3_mcart_1(A_1259,B_1257,C_1258),k3_mcart_1(A_1259,C_1255,C_1258)),k3_zfmisc_1(k1_tarski(A_1259),k2_tarski(B_1257,C_1255),k1_tarski(B_1256))) = k3_zfmisc_1(k1_tarski(A_1259),k2_tarski(B_1257,C_1255),k2_tarski(C_1258,B_1256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_387])).

tff(c_73833,plain,(
    ! [C_1258,B_33,C_34,C_153,A_32] : k2_enumset1(k3_mcart_1(A_32,B_33,C_1258),k3_mcart_1(A_32,C_34,C_1258),k3_mcart_1(A_32,B_33,C_153),k3_mcart_1(A_32,C_34,C_153)) = k3_zfmisc_1(k1_tarski(A_32),k2_tarski(B_33,C_34),k2_tarski(C_1258,C_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2633,c_73702])).

tff(c_18,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_2','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_2','#skF_5'),k3_mcart_1('#skF_1','#skF_3','#skF_5')) != k3_zfmisc_1(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73833,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.74/29.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.74/29.82  
% 41.74/29.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.74/29.82  %$ k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 41.74/29.82  
% 41.74/29.82  %Foreground sorts:
% 41.74/29.82  
% 41.74/29.82  
% 41.74/29.82  %Background operators:
% 41.74/29.82  
% 41.74/29.82  
% 41.74/29.82  %Foreground operators:
% 41.74/29.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.74/29.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 41.74/29.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 41.74/29.82  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 41.74/29.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 41.74/29.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 41.74/29.82  tff('#skF_5', type, '#skF_5': $i).
% 41.74/29.82  tff('#skF_2', type, '#skF_2': $i).
% 41.74/29.82  tff('#skF_3', type, '#skF_3': $i).
% 41.74/29.82  tff('#skF_1', type, '#skF_1': $i).
% 41.74/29.82  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 41.74/29.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.74/29.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 41.74/29.82  tff('#skF_4', type, '#skF_4': $i).
% 41.74/29.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.74/29.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.74/29.82  
% 41.74/29.84  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 41.74/29.84  tff(f_37, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 41.74/29.84  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 41.74/29.84  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 41.74/29.84  tff(f_33, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 41.74/29.84  tff(f_44, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k1_tarski(A), k2_tarski(B, C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, B, D), k3_mcart_1(A, C, D), k3_mcart_1(A, B, E), k3_mcart_1(A, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_mcart_1)).
% 41.74/29.84  tff(c_14, plain, (![A_12, B_13, C_14]: (k4_tarski(k4_tarski(A_12, B_13), C_14)=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 41.74/29.84  tff(c_93, plain, (![A_32, B_33, C_34]: (k2_zfmisc_1(k1_tarski(A_32), k2_tarski(B_33, C_34))=k2_tarski(k4_tarski(A_32, B_33), k4_tarski(A_32, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.74/29.84  tff(c_16, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.74/29.84  tff(c_114, plain, (![A_32, B_33, C_34, C_17]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_32, B_33), k4_tarski(A_32, C_34)), C_17)=k3_zfmisc_1(k1_tarski(A_32), k2_tarski(B_33, C_34), C_17))), inference(superposition, [status(thm), theory('equality')], [c_93, c_16])).
% 41.74/29.84  tff(c_265, plain, (![A_50, B_51, C_52]: (k2_zfmisc_1(k2_tarski(A_50, B_51), k1_tarski(C_52))=k2_tarski(k4_tarski(A_50, C_52), k4_tarski(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.74/29.84  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.74/29.84  tff(c_2443, plain, (![A_152, B_155, A_156, C_153, B_154]: (k2_xboole_0(k2_tarski(A_156, B_155), k2_zfmisc_1(k2_tarski(A_152, B_154), k1_tarski(C_153)))=k2_enumset1(A_156, B_155, k4_tarski(A_152, C_153), k4_tarski(B_154, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 41.74/29.84  tff(c_2552, plain, (![B_155, B_33, A_156, C_34, C_153, A_32]: (k2_xboole_0(k2_tarski(A_156, B_155), k3_zfmisc_1(k1_tarski(A_32), k2_tarski(B_33, C_34), k1_tarski(C_153)))=k2_enumset1(A_156, B_155, k4_tarski(k4_tarski(A_32, B_33), C_153), k4_tarski(k4_tarski(A_32, C_34), C_153)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2443])).
% 41.74/29.84  tff(c_2633, plain, (![B_155, B_33, A_156, C_34, C_153, A_32]: (k2_xboole_0(k2_tarski(A_156, B_155), k3_zfmisc_1(k1_tarski(A_32), k2_tarski(B_33, C_34), k1_tarski(C_153)))=k2_enumset1(A_156, B_155, k3_mcart_1(A_32, B_33, C_153), k3_mcart_1(A_32, C_34, C_153)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_2552])).
% 41.74/29.84  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k1_tarski(A_9), k2_tarski(B_10, C_11))=k2_tarski(k4_tarski(A_9, B_10), k4_tarski(A_9, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.74/29.84  tff(c_315, plain, (![A_9, B_10, C_11, C_52]: (k2_zfmisc_1(k2_zfmisc_1(k1_tarski(A_9), k2_tarski(B_10, C_11)), k1_tarski(C_52))=k2_tarski(k4_tarski(k4_tarski(A_9, B_10), C_52), k4_tarski(k4_tarski(A_9, C_11), C_52)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_265])).
% 41.74/29.84  tff(c_1309, plain, (![A_114, B_115, C_116, C_117]: (k3_zfmisc_1(k1_tarski(A_114), k2_tarski(B_115, C_116), k1_tarski(C_117))=k2_tarski(k3_mcart_1(A_114, B_115, C_117), k3_mcart_1(A_114, C_116, C_117)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16, c_315])).
% 41.74/29.84  tff(c_355, plain, (![C_56, A_57, B_58]: (k2_xboole_0(k2_zfmisc_1(C_56, k1_tarski(A_57)), k2_zfmisc_1(C_56, k1_tarski(B_58)))=k2_zfmisc_1(C_56, k2_tarski(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 41.74/29.84  tff(c_381, plain, (![A_15, B_16, A_57, B_58]: (k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), k1_tarski(A_57)), k3_zfmisc_1(A_15, B_16, k1_tarski(B_58)))=k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_355])).
% 41.74/29.84  tff(c_387, plain, (![A_15, B_16, A_57, B_58]: (k2_xboole_0(k3_zfmisc_1(A_15, B_16, k1_tarski(A_57)), k3_zfmisc_1(A_15, B_16, k1_tarski(B_58)))=k3_zfmisc_1(A_15, B_16, k2_tarski(A_57, B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_381])).
% 41.74/29.84  tff(c_73702, plain, (![C_1258, C_1255, B_1257, B_1256, A_1259]: (k2_xboole_0(k2_tarski(k3_mcart_1(A_1259, B_1257, C_1258), k3_mcart_1(A_1259, C_1255, C_1258)), k3_zfmisc_1(k1_tarski(A_1259), k2_tarski(B_1257, C_1255), k1_tarski(B_1256)))=k3_zfmisc_1(k1_tarski(A_1259), k2_tarski(B_1257, C_1255), k2_tarski(C_1258, B_1256)))), inference(superposition, [status(thm), theory('equality')], [c_1309, c_387])).
% 41.74/29.84  tff(c_73833, plain, (![C_1258, B_33, C_34, C_153, A_32]: (k2_enumset1(k3_mcart_1(A_32, B_33, C_1258), k3_mcart_1(A_32, C_34, C_1258), k3_mcart_1(A_32, B_33, C_153), k3_mcart_1(A_32, C_34, C_153))=k3_zfmisc_1(k1_tarski(A_32), k2_tarski(B_33, C_34), k2_tarski(C_1258, C_153)))), inference(superposition, [status(thm), theory('equality')], [c_2633, c_73702])).
% 41.74/29.84  tff(c_18, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_2', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_2', '#skF_5'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 41.74/29.84  tff(c_74419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73833, c_18])).
% 41.74/29.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.74/29.84  
% 41.74/29.84  Inference rules
% 41.74/29.84  ----------------------
% 41.74/29.84  #Ref     : 0
% 41.74/29.84  #Sup     : 18416
% 41.74/29.84  #Fact    : 0
% 41.74/29.84  #Define  : 0
% 41.74/29.84  #Split   : 0
% 41.74/29.84  #Chain   : 0
% 41.74/29.84  #Close   : 0
% 41.74/29.84  
% 41.74/29.84  Ordering : KBO
% 41.74/29.84  
% 41.74/29.84  Simplification rules
% 41.74/29.84  ----------------------
% 41.74/29.84  #Subsume      : 2135
% 41.74/29.84  #Demod        : 30081
% 41.74/29.84  #Tautology    : 4623
% 41.74/29.84  #SimpNegUnit  : 0
% 41.74/29.84  #BackRed      : 1
% 41.74/29.84  
% 41.74/29.84  #Partial instantiations: 0
% 41.74/29.84  #Strategies tried      : 1
% 41.74/29.84  
% 41.74/29.84  Timing (in seconds)
% 41.74/29.84  ----------------------
% 41.74/29.84  Preprocessing        : 0.28
% 41.74/29.84  Parsing              : 0.15
% 41.74/29.84  CNF conversion       : 0.01
% 41.74/29.84  Main loop            : 28.78
% 41.74/29.84  Inferencing          : 5.83
% 41.74/29.84  Reduction            : 18.01
% 41.74/29.84  Demodulation         : 16.77
% 41.74/29.84  BG Simplification    : 0.96
% 41.74/29.84  Subsumption          : 3.32
% 41.74/29.84  Abstraction          : 2.10
% 41.74/29.84  MUC search           : 0.00
% 41.74/29.84  Cooper               : 0.00
% 41.74/29.84  Total                : 29.08
% 41.74/29.84  Index Insertion      : 0.00
% 41.74/29.84  Index Deletion       : 0.00
% 41.74/29.84  Index Matching       : 0.00
% 41.74/29.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
