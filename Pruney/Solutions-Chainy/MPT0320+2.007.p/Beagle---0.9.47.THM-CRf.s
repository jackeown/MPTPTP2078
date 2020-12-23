%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:12 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  69 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  55 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_52,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_24,B_25] : k2_enumset1(A_24,A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [B_39,C_40] : k1_enumset1(B_39,B_39,C_40) = k2_tarski(B_39,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_10,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_43,B_44,C_45,D_46] : k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k1_tarski(D_46)) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [B_39,C_40,D_46] : k2_xboole_0(k2_tarski(B_39,C_40),k1_tarski(D_46)) = k2_enumset1(B_39,B_39,C_40,D_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_77])).

tff(c_91,plain,(
    ! [B_47,C_48,D_49] : k2_xboole_0(k2_tarski(B_47,C_48),k1_tarski(D_49)) = k1_enumset1(B_47,C_48,D_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_86])).

tff(c_100,plain,(
    ! [A_20,D_49] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_49)) = k1_enumset1(A_20,A_20,D_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_91])).

tff(c_103,plain,(
    ! [A_20,D_49] : k2_xboole_0(k1_tarski(A_20),k1_tarski(D_49)) = k2_tarski(A_20,D_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_100])).

tff(c_18,plain,(
    ! [A_30,C_32,B_31] : k2_xboole_0(k2_zfmisc_1(A_30,C_32),k2_zfmisc_1(B_31,C_32)) = k2_zfmisc_1(k2_xboole_0(A_30,B_31),C_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [C_32,A_30,B_31] : k2_xboole_0(k2_zfmisc_1(C_32,A_30),k2_zfmisc_1(C_32,B_31)) = k2_zfmisc_1(C_32,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_24,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_23])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.20  
% 1.82/1.20  %Foreground sorts:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Background operators:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Foreground operators:
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.20  
% 1.82/1.21  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.82/1.21  tff(f_39, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 1.82/1.21  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/1.21  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.82/1.21  tff(f_45, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.82/1.21  tff(f_50, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 1.82/1.21  tff(c_52, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.21  tff(c_14, plain, (![A_24, B_25]: (k2_enumset1(A_24, A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.21  tff(c_59, plain, (![B_39, C_40]: (k1_enumset1(B_39, B_39, C_40)=k2_tarski(B_39, C_40))), inference(superposition, [status(thm), theory('equality')], [c_52, c_14])).
% 1.82/1.21  tff(c_10, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.21  tff(c_12, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.21  tff(c_77, plain, (![A_43, B_44, C_45, D_46]: (k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k1_tarski(D_46))=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.21  tff(c_86, plain, (![B_39, C_40, D_46]: (k2_xboole_0(k2_tarski(B_39, C_40), k1_tarski(D_46))=k2_enumset1(B_39, B_39, C_40, D_46))), inference(superposition, [status(thm), theory('equality')], [c_59, c_77])).
% 1.82/1.21  tff(c_91, plain, (![B_47, C_48, D_49]: (k2_xboole_0(k2_tarski(B_47, C_48), k1_tarski(D_49))=k1_enumset1(B_47, C_48, D_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_86])).
% 1.82/1.21  tff(c_100, plain, (![A_20, D_49]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_49))=k1_enumset1(A_20, A_20, D_49))), inference(superposition, [status(thm), theory('equality')], [c_10, c_91])).
% 1.82/1.21  tff(c_103, plain, (![A_20, D_49]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(D_49))=k2_tarski(A_20, D_49))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_100])).
% 1.82/1.21  tff(c_18, plain, (![A_30, C_32, B_31]: (k2_xboole_0(k2_zfmisc_1(A_30, C_32), k2_zfmisc_1(B_31, C_32))=k2_zfmisc_1(k2_xboole_0(A_30, B_31), C_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.21  tff(c_20, plain, (![C_32, A_30, B_31]: (k2_xboole_0(k2_zfmisc_1(C_32, A_30), k2_zfmisc_1(C_32, B_31))=k2_zfmisc_1(C_32, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.21  tff(c_22, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.21  tff(c_23, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 1.82/1.21  tff(c_24, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_23])).
% 1.82/1.21  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_24])).
% 1.82/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  Inference rules
% 1.82/1.21  ----------------------
% 1.82/1.21  #Ref     : 0
% 1.82/1.21  #Sup     : 20
% 1.82/1.21  #Fact    : 0
% 1.82/1.21  #Define  : 0
% 1.82/1.21  #Split   : 0
% 1.82/1.21  #Chain   : 0
% 1.82/1.21  #Close   : 0
% 1.82/1.21  
% 1.82/1.21  Ordering : KBO
% 1.82/1.21  
% 1.82/1.21  Simplification rules
% 1.82/1.21  ----------------------
% 1.82/1.21  #Subsume      : 0
% 1.82/1.21  #Demod        : 7
% 1.82/1.21  #Tautology    : 17
% 1.82/1.21  #SimpNegUnit  : 0
% 1.82/1.21  #BackRed      : 0
% 1.82/1.21  
% 1.82/1.21  #Partial instantiations: 0
% 1.82/1.21  #Strategies tried      : 1
% 1.82/1.21  
% 1.82/1.21  Timing (in seconds)
% 1.82/1.21  ----------------------
% 1.82/1.21  Preprocessing        : 0.29
% 1.82/1.21  Parsing              : 0.15
% 1.82/1.21  CNF conversion       : 0.02
% 1.82/1.21  Main loop            : 0.09
% 1.82/1.21  Inferencing          : 0.03
% 1.82/1.21  Reduction            : 0.03
% 1.82/1.21  Demodulation         : 0.03
% 1.82/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.01
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.40
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
