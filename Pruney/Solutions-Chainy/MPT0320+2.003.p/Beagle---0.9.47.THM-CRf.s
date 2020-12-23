%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  60 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_476,plain,(
    ! [A_49,B_50,C_51,D_52] : k2_xboole_0(k1_enumset1(A_49,B_50,C_51),k1_tarski(D_52)) = k2_enumset1(A_49,B_50,C_51,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_485,plain,(
    ! [A_6,B_7,D_52] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(D_52)) = k2_enumset1(A_6,A_6,B_7,D_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_476])).

tff(c_489,plain,(
    ! [A_53,B_54,D_55] : k2_xboole_0(k2_tarski(A_53,B_54),k1_tarski(D_55)) = k1_enumset1(A_53,B_54,D_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_485])).

tff(c_498,plain,(
    ! [A_5,D_55] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_55)) = k1_enumset1(A_5,A_5,D_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_489])).

tff(c_501,plain,(
    ! [A_5,D_55] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_55)) = k2_tarski(A_5,D_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_498])).

tff(c_144,plain,(
    ! [A_32,B_33,C_34,D_35] : k2_xboole_0(k1_enumset1(A_32,B_33,C_34),k1_tarski(D_35)) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_6,B_7,D_35] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(D_35)) = k2_enumset1(A_6,A_6,B_7,D_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_157,plain,(
    ! [A_36,B_37,D_38] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(D_38)) = k1_enumset1(A_36,B_37,D_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_153])).

tff(c_166,plain,(
    ! [A_5,D_38] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_38)) = k1_enumset1(A_5,A_5,D_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_169,plain,(
    ! [A_5,D_38] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_38)) = k2_tarski(A_5,D_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_12,plain,(
    ! [A_13,C_15,B_14] : k2_xboole_0(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,C_15)) = k2_zfmisc_1(k2_xboole_0(A_13,B_14),C_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] : k2_xboole_0(k2_zfmisc_1(C_15,A_13),k2_zfmisc_1(C_15,B_14)) = k2_zfmisc_1(C_15,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_18,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_17])).

tff(c_143,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_143])).

tff(c_474,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:57:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.51/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.38  
% 2.51/1.39  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.51/1.39  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.51/1.39  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.51/1.39  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.51/1.39  tff(f_39, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 2.51/1.39  tff(f_44, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 2.51/1.39  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.39  tff(c_4, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.39  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.39  tff(c_476, plain, (![A_49, B_50, C_51, D_52]: (k2_xboole_0(k1_enumset1(A_49, B_50, C_51), k1_tarski(D_52))=k2_enumset1(A_49, B_50, C_51, D_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.39  tff(c_485, plain, (![A_6, B_7, D_52]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(D_52))=k2_enumset1(A_6, A_6, B_7, D_52))), inference(superposition, [status(thm), theory('equality')], [c_6, c_476])).
% 2.51/1.39  tff(c_489, plain, (![A_53, B_54, D_55]: (k2_xboole_0(k2_tarski(A_53, B_54), k1_tarski(D_55))=k1_enumset1(A_53, B_54, D_55))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_485])).
% 2.51/1.39  tff(c_498, plain, (![A_5, D_55]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_55))=k1_enumset1(A_5, A_5, D_55))), inference(superposition, [status(thm), theory('equality')], [c_4, c_489])).
% 2.51/1.39  tff(c_501, plain, (![A_5, D_55]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_55))=k2_tarski(A_5, D_55))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_498])).
% 2.51/1.39  tff(c_144, plain, (![A_32, B_33, C_34, D_35]: (k2_xboole_0(k1_enumset1(A_32, B_33, C_34), k1_tarski(D_35))=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.39  tff(c_153, plain, (![A_6, B_7, D_35]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(D_35))=k2_enumset1(A_6, A_6, B_7, D_35))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 2.51/1.39  tff(c_157, plain, (![A_36, B_37, D_38]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(D_38))=k1_enumset1(A_36, B_37, D_38))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_153])).
% 2.51/1.39  tff(c_166, plain, (![A_5, D_38]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_38))=k1_enumset1(A_5, A_5, D_38))), inference(superposition, [status(thm), theory('equality')], [c_4, c_157])).
% 2.51/1.39  tff(c_169, plain, (![A_5, D_38]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_38))=k2_tarski(A_5, D_38))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 2.51/1.39  tff(c_12, plain, (![A_13, C_15, B_14]: (k2_xboole_0(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, C_15))=k2_zfmisc_1(k2_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.39  tff(c_14, plain, (![C_15, A_13, B_14]: (k2_xboole_0(k2_zfmisc_1(C_15, A_13), k2_zfmisc_1(C_15, B_14))=k2_zfmisc_1(C_15, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.39  tff(c_16, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.39  tff(c_17, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.51/1.39  tff(c_18, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_17])).
% 2.51/1.39  tff(c_143, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.51/1.39  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_143])).
% 2.51/1.39  tff(c_474, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 2.51/1.39  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_474])).
% 2.51/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.39  
% 2.51/1.39  Inference rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Ref     : 0
% 2.51/1.39  #Sup     : 128
% 2.51/1.39  #Fact    : 0
% 2.51/1.39  #Define  : 0
% 2.51/1.39  #Split   : 1
% 2.51/1.39  #Chain   : 0
% 2.51/1.39  #Close   : 0
% 2.51/1.39  
% 2.51/1.39  Ordering : KBO
% 2.51/1.39  
% 2.51/1.39  Simplification rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Subsume      : 8
% 2.51/1.39  #Demod        : 49
% 2.51/1.39  #Tautology    : 48
% 2.51/1.39  #SimpNegUnit  : 0
% 2.51/1.39  #BackRed      : 0
% 2.51/1.39  
% 2.51/1.39  #Partial instantiations: 0
% 2.51/1.39  #Strategies tried      : 1
% 2.51/1.39  
% 2.51/1.39  Timing (in seconds)
% 2.51/1.39  ----------------------
% 2.51/1.39  Preprocessing        : 0.28
% 2.51/1.39  Parsing              : 0.15
% 2.51/1.39  CNF conversion       : 0.02
% 2.51/1.39  Main loop            : 0.26
% 2.51/1.39  Inferencing          : 0.09
% 2.51/1.39  Reduction            : 0.10
% 2.51/1.39  Demodulation         : 0.09
% 2.51/1.39  BG Simplification    : 0.02
% 2.51/1.39  Subsumption          : 0.04
% 2.51/1.39  Abstraction          : 0.02
% 2.51/1.39  MUC search           : 0.00
% 2.51/1.39  Cooper               : 0.00
% 2.51/1.39  Total                : 0.58
% 2.51/1.39  Index Insertion      : 0.00
% 2.51/1.39  Index Deletion       : 0.00
% 2.51/1.39  Index Matching       : 0.00
% 2.51/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
