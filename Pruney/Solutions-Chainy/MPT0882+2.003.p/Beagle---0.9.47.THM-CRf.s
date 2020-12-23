%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:31 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  47 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k2_tarski(C,D)) = k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(A,B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_mcart_1)).

tff(c_100,plain,(
    ! [A_62,B_63,C_64,D_65] : k4_tarski(k3_mcart_1(A_62,B_63,C_64),D_65) = k4_mcart_1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_43,B_44] : k1_mcart_1(k4_tarski(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_62,B_63,C_64,D_65] : k1_mcart_1(k4_mcart_1(A_62,B_63,C_64,D_65)) = k3_mcart_1(A_62,B_63,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_26])).

tff(c_133,plain,(
    ! [A_74,B_75,C_76,D_77] : k4_tarski(k4_tarski(k4_tarski(A_74,B_75),C_76),D_77) = k4_mcart_1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_145,plain,(
    ! [A_74,B_75,C_76,D_77] : k4_tarski(k4_tarski(A_74,B_75),C_76) = k1_mcart_1(k4_mcart_1(A_74,B_75,C_76,D_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_26])).

tff(c_162,plain,(
    ! [A_74,B_75,C_76] : k4_tarski(k4_tarski(A_74,B_75),C_76) = k3_mcart_1(A_74,B_75,C_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_145])).

tff(c_345,plain,(
    ! [A_108,B_109,C_110] : k2_zfmisc_1(k1_tarski(A_108),k2_tarski(B_109,C_110)) = k2_tarski(k4_tarski(A_108,B_109),k4_tarski(A_108,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_393,plain,(
    ! [A_74,B_75,B_109,C_76] : k2_zfmisc_1(k1_tarski(k4_tarski(A_74,B_75)),k2_tarski(B_109,C_76)) = k2_tarski(k4_tarski(k4_tarski(A_74,B_75),B_109),k3_mcart_1(A_74,B_75,C_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_345])).

tff(c_416,plain,(
    ! [A_74,B_75,B_109,C_76] : k2_zfmisc_1(k1_tarski(k4_tarski(A_74,B_75)),k2_tarski(B_109,C_76)) = k2_tarski(k3_mcart_1(A_74,B_75,B_109),k3_mcart_1(A_74,B_75,C_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_393])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_260,plain,(
    ! [A_100,B_101,C_102] : k2_zfmisc_1(k2_tarski(A_100,B_101),k1_tarski(C_102)) = k2_tarski(k4_tarski(A_100,C_102),k4_tarski(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_279,plain,(
    ! [B_101,C_102] : k2_zfmisc_1(k2_tarski(B_101,B_101),k1_tarski(C_102)) = k1_tarski(k4_tarski(B_101,C_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_2])).

tff(c_317,plain,(
    ! [B_103,C_104] : k2_zfmisc_1(k1_tarski(B_103),k1_tarski(C_104)) = k1_tarski(k4_tarski(B_103,C_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_20,plain,(
    ! [A_32,B_33,C_34] : k2_zfmisc_1(k2_zfmisc_1(A_32,B_33),C_34) = k3_zfmisc_1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_326,plain,(
    ! [B_103,C_104,C_34] : k3_zfmisc_1(k1_tarski(B_103),k1_tarski(C_104),C_34) = k2_zfmisc_1(k1_tarski(k4_tarski(B_103,C_104)),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_20])).

tff(c_30,plain,(
    k3_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_335,plain,(
    k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1','#skF_2')),k2_tarski('#skF_3','#skF_4')) != k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_1199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.52  
% 3.37/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.53  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.37/1.53  
% 3.37/1.53  %Foreground sorts:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Background operators:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Foreground operators:
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.37/1.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.37/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.37/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.37/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.37/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.53  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.37/1.53  
% 3.59/1.54  tff(f_47, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 3.59/1.54  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.59/1.54  tff(f_49, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 3.59/1.54  tff(f_43, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.59/1.54  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.59/1.54  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.59/1.54  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k2_tarski(C, D)) = k2_tarski(k3_mcart_1(A, B, C), k3_mcart_1(A, B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_mcart_1)).
% 3.59/1.54  tff(c_100, plain, (![A_62, B_63, C_64, D_65]: (k4_tarski(k3_mcart_1(A_62, B_63, C_64), D_65)=k4_mcart_1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.59/1.54  tff(c_26, plain, (![A_43, B_44]: (k1_mcart_1(k4_tarski(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.59/1.54  tff(c_106, plain, (![A_62, B_63, C_64, D_65]: (k1_mcart_1(k4_mcart_1(A_62, B_63, C_64, D_65))=k3_mcart_1(A_62, B_63, C_64))), inference(superposition, [status(thm), theory('equality')], [c_100, c_26])).
% 3.59/1.54  tff(c_133, plain, (![A_74, B_75, C_76, D_77]: (k4_tarski(k4_tarski(k4_tarski(A_74, B_75), C_76), D_77)=k4_mcart_1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.59/1.54  tff(c_145, plain, (![A_74, B_75, C_76, D_77]: (k4_tarski(k4_tarski(A_74, B_75), C_76)=k1_mcart_1(k4_mcart_1(A_74, B_75, C_76, D_77)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_26])).
% 3.59/1.54  tff(c_162, plain, (![A_74, B_75, C_76]: (k4_tarski(k4_tarski(A_74, B_75), C_76)=k3_mcart_1(A_74, B_75, C_76))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_145])).
% 3.59/1.54  tff(c_345, plain, (![A_108, B_109, C_110]: (k2_zfmisc_1(k1_tarski(A_108), k2_tarski(B_109, C_110))=k2_tarski(k4_tarski(A_108, B_109), k4_tarski(A_108, C_110)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/1.54  tff(c_393, plain, (![A_74, B_75, B_109, C_76]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_74, B_75)), k2_tarski(B_109, C_76))=k2_tarski(k4_tarski(k4_tarski(A_74, B_75), B_109), k3_mcart_1(A_74, B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_345])).
% 3.59/1.54  tff(c_416, plain, (![A_74, B_75, B_109, C_76]: (k2_zfmisc_1(k1_tarski(k4_tarski(A_74, B_75)), k2_tarski(B_109, C_76))=k2_tarski(k3_mcart_1(A_74, B_75, B_109), k3_mcart_1(A_74, B_75, C_76)))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_393])).
% 3.59/1.54  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.59/1.54  tff(c_260, plain, (![A_100, B_101, C_102]: (k2_zfmisc_1(k2_tarski(A_100, B_101), k1_tarski(C_102))=k2_tarski(k4_tarski(A_100, C_102), k4_tarski(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/1.54  tff(c_279, plain, (![B_101, C_102]: (k2_zfmisc_1(k2_tarski(B_101, B_101), k1_tarski(C_102))=k1_tarski(k4_tarski(B_101, C_102)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_2])).
% 3.59/1.54  tff(c_317, plain, (![B_103, C_104]: (k2_zfmisc_1(k1_tarski(B_103), k1_tarski(C_104))=k1_tarski(k4_tarski(B_103, C_104)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_279])).
% 3.59/1.54  tff(c_20, plain, (![A_32, B_33, C_34]: (k2_zfmisc_1(k2_zfmisc_1(A_32, B_33), C_34)=k3_zfmisc_1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.59/1.54  tff(c_326, plain, (![B_103, C_104, C_34]: (k3_zfmisc_1(k1_tarski(B_103), k1_tarski(C_104), C_34)=k2_zfmisc_1(k1_tarski(k4_tarski(B_103, C_104)), C_34))), inference(superposition, [status(thm), theory('equality')], [c_317, c_20])).
% 3.59/1.54  tff(c_30, plain, (k3_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.59/1.54  tff(c_335, plain, (k2_zfmisc_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_3', '#skF_4'))!=k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_30])).
% 3.59/1.54  tff(c_1199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_335])).
% 3.59/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.54  
% 3.59/1.54  Inference rules
% 3.59/1.54  ----------------------
% 3.59/1.54  #Ref     : 0
% 3.59/1.54  #Sup     : 285
% 3.59/1.54  #Fact    : 0
% 3.59/1.54  #Define  : 0
% 3.59/1.54  #Split   : 0
% 3.59/1.54  #Chain   : 0
% 3.59/1.54  #Close   : 0
% 3.59/1.54  
% 3.59/1.54  Ordering : KBO
% 3.59/1.54  
% 3.59/1.54  Simplification rules
% 3.59/1.54  ----------------------
% 3.59/1.54  #Subsume      : 12
% 3.59/1.54  #Demod        : 232
% 3.59/1.54  #Tautology    : 156
% 3.59/1.54  #SimpNegUnit  : 0
% 3.59/1.54  #BackRed      : 3
% 3.59/1.54  
% 3.59/1.54  #Partial instantiations: 0
% 3.59/1.54  #Strategies tried      : 1
% 3.59/1.54  
% 3.59/1.54  Timing (in seconds)
% 3.59/1.54  ----------------------
% 3.59/1.54  Preprocessing        : 0.31
% 3.59/1.54  Parsing              : 0.16
% 3.59/1.54  CNF conversion       : 0.02
% 3.59/1.54  Main loop            : 0.48
% 3.59/1.54  Inferencing          : 0.19
% 3.59/1.54  Reduction            : 0.18
% 3.59/1.54  Demodulation         : 0.15
% 3.59/1.54  BG Simplification    : 0.03
% 3.59/1.54  Subsumption          : 0.05
% 3.59/1.54  Abstraction          : 0.05
% 3.59/1.54  MUC search           : 0.00
% 3.59/1.54  Cooper               : 0.00
% 3.59/1.54  Total                : 0.81
% 3.59/1.54  Index Insertion      : 0.00
% 3.59/1.54  Index Deletion       : 0.00
% 3.59/1.54  Index Matching       : 0.00
% 3.59/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
