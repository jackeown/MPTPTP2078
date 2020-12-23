%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 198 expanded)
%              Number of leaves         :   26 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 272 expanded)
%              Number of equality atoms :   45 ( 232 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_37,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_172,plain,(
    ! [A_51,B_52,C_53] : k2_zfmisc_1(k1_tarski(A_51),k2_tarski(B_52,C_53)) = k2_tarski(k4_tarski(A_51,B_52),k4_tarski(A_51,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_194,plain,(
    ! [A_51,C_53] : k2_zfmisc_1(k1_tarski(A_51),k2_tarski(C_53,C_53)) = k1_tarski(k4_tarski(A_51,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_4])).

tff(c_237,plain,(
    ! [A_59,C_60] : k2_zfmisc_1(k1_tarski(A_59),k1_tarski(C_60)) = k1_tarski(k4_tarski(A_59,C_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1(k2_zfmisc_1(A_18,B_19)) = A_18
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,(
    ! [A_59,C_60] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_59,C_60))) = k1_tarski(A_59)
      | k1_tarski(C_60) = k1_xboole_0
      | k1_tarski(A_59) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_26])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22] : k4_tarski(k4_tarski(A_20,B_21),C_22) = k3_mcart_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_401,plain,(
    ! [A_87,C_88] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_87,C_88))) = k1_tarski(A_87)
      | k1_tarski(C_88) = k1_xboole_0
      | k1_tarski(A_87) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_26])).

tff(c_1967,plain,(
    ! [A_281,B_282,C_283] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_281,B_282,C_283))) = k1_tarski(k4_tarski(A_281,B_282))
      | k1_tarski(C_283) = k1_xboole_0
      | k1_tarski(k4_tarski(A_281,B_282)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_401])).

tff(c_30,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1973,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1')
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_30])).

tff(c_1983,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1973])).

tff(c_1987,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1983])).

tff(c_1988,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1987])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k2_tarski(k4_tarski(A_15,C_17),k4_tarski(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k1_tarski(A_15),k2_tarski(B_16,C_17)) = k2_tarski(k4_tarski(A_15,B_16),k4_tarski(A_15,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_11,B_12] : ~ v1_xboole_0(k2_tarski(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_228,plain,(
    ! [A_54,B_55,C_56] : ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(A_54),k2_tarski(B_55,C_56))) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_12])).

tff(c_373,plain,(
    ! [A_79,A_80,B_81,C_82] : ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(A_79),k2_zfmisc_1(k1_tarski(A_80),k2_tarski(B_81,C_82)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_228])).

tff(c_495,plain,(
    ! [A_123,C_122,A_126,B_124,A_125] : ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(A_125),k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_tarski(B_124,C_122))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_373])).

tff(c_497,plain,(
    ! [B_16,A_15,A_123,A_126,A_125,C_17] : ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(A_125),k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_495])).

tff(c_2011,plain,(
    ! [B_16,A_15,A_123,A_126,C_17] : ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1988,c_497])).

tff(c_2236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_2011])).

tff(c_2237,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1987])).

tff(c_2259,plain,(
    ! [B_16,A_15,A_123,A_126,C_17] : ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_497])).

tff(c_2484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_2259])).

tff(c_2485,plain,
    ( k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1973])).

tff(c_2499,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2485])).

tff(c_2520,plain,(
    ! [B_16,A_15,A_123,A_126,C_17] : ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2499,c_497])).

tff(c_2745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_2520])).

tff(c_2746,plain,(
    k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2485])).

tff(c_2763,plain,(
    ! [B_16,A_15,A_123,A_126,C_17] : ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_123),k2_zfmisc_1(k1_tarski(A_126),k2_zfmisc_1(k2_tarski(A_15,B_16),k1_tarski(C_17)))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2746,c_497])).

tff(c_2992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_2763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.89  
% 4.67/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.89  %$ v1_xboole_0 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.67/1.89  
% 4.67/1.89  %Foreground sorts:
% 4.67/1.89  
% 4.67/1.89  
% 4.67/1.89  %Background operators:
% 4.67/1.89  
% 4.67/1.89  
% 4.67/1.89  %Foreground operators:
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.67/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.89  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.67/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.67/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.67/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.67/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.67/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.67/1.89  
% 4.67/1.90  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.67/1.90  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.67/1.90  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.67/1.90  tff(f_47, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 4.67/1.90  tff(f_59, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 4.67/1.90  tff(f_61, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.67/1.90  tff(f_64, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 4.67/1.90  tff(f_37, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 4.67/1.90  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.67/1.90  tff(c_18, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.67/1.90  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.67/1.90  tff(c_172, plain, (![A_51, B_52, C_53]: (k2_zfmisc_1(k1_tarski(A_51), k2_tarski(B_52, C_53))=k2_tarski(k4_tarski(A_51, B_52), k4_tarski(A_51, C_53)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.90  tff(c_194, plain, (![A_51, C_53]: (k2_zfmisc_1(k1_tarski(A_51), k2_tarski(C_53, C_53))=k1_tarski(k4_tarski(A_51, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_4])).
% 4.67/1.90  tff(c_237, plain, (![A_59, C_60]: (k2_zfmisc_1(k1_tarski(A_59), k1_tarski(C_60))=k1_tarski(k4_tarski(A_59, C_60)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_194])).
% 4.67/1.90  tff(c_26, plain, (![A_18, B_19]: (k1_relat_1(k2_zfmisc_1(A_18, B_19))=A_18 | k1_xboole_0=B_19 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.67/1.90  tff(c_246, plain, (![A_59, C_60]: (k1_relat_1(k1_tarski(k4_tarski(A_59, C_60)))=k1_tarski(A_59) | k1_tarski(C_60)=k1_xboole_0 | k1_tarski(A_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_26])).
% 4.67/1.90  tff(c_28, plain, (![A_20, B_21, C_22]: (k4_tarski(k4_tarski(A_20, B_21), C_22)=k3_mcart_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.67/1.90  tff(c_401, plain, (![A_87, C_88]: (k1_relat_1(k1_tarski(k4_tarski(A_87, C_88)))=k1_tarski(A_87) | k1_tarski(C_88)=k1_xboole_0 | k1_tarski(A_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_237, c_26])).
% 4.67/1.90  tff(c_1967, plain, (![A_281, B_282, C_283]: (k1_relat_1(k1_tarski(k3_mcart_1(A_281, B_282, C_283)))=k1_tarski(k4_tarski(A_281, B_282)) | k1_tarski(C_283)=k1_xboole_0 | k1_tarski(k4_tarski(A_281, B_282))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_401])).
% 4.67/1.90  tff(c_30, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.90  tff(c_1973, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1') | k1_tarski('#skF_3')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1967, c_30])).
% 4.67/1.90  tff(c_1983, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_1973])).
% 4.67/1.90  tff(c_1987, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_246, c_1983])).
% 4.67/1.90  tff(c_1988, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1987])).
% 4.67/1.90  tff(c_22, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17))=k2_tarski(k4_tarski(A_15, C_17), k4_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.90  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k1_tarski(A_15), k2_tarski(B_16, C_17))=k2_tarski(k4_tarski(A_15, B_16), k4_tarski(A_15, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.90  tff(c_12, plain, (![A_11, B_12]: (~v1_xboole_0(k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.67/1.90  tff(c_228, plain, (![A_54, B_55, C_56]: (~v1_xboole_0(k2_zfmisc_1(k1_tarski(A_54), k2_tarski(B_55, C_56))))), inference(superposition, [status(thm), theory('equality')], [c_172, c_12])).
% 4.67/1.90  tff(c_373, plain, (![A_79, A_80, B_81, C_82]: (~v1_xboole_0(k2_zfmisc_1(k1_tarski(A_79), k2_zfmisc_1(k1_tarski(A_80), k2_tarski(B_81, C_82)))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_228])).
% 4.67/1.90  tff(c_495, plain, (![A_123, C_122, A_126, B_124, A_125]: (~v1_xboole_0(k2_zfmisc_1(k1_tarski(A_125), k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_tarski(B_124, C_122))))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_373])).
% 4.67/1.90  tff(c_497, plain, (![B_16, A_15, A_123, A_126, A_125, C_17]: (~v1_xboole_0(k2_zfmisc_1(k1_tarski(A_125), k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17)))))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_495])).
% 4.67/1.90  tff(c_2011, plain, (![B_16, A_15, A_123, A_126, C_17]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17)))))))), inference(superposition, [status(thm), theory('equality')], [c_1988, c_497])).
% 4.67/1.90  tff(c_2236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_2011])).
% 4.67/1.90  tff(c_2237, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1987])).
% 4.67/1.90  tff(c_2259, plain, (![B_16, A_15, A_123, A_126, C_17]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17)))))))), inference(superposition, [status(thm), theory('equality')], [c_2237, c_497])).
% 4.67/1.90  tff(c_2484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_2259])).
% 4.67/1.90  tff(c_2485, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1973])).
% 4.67/1.90  tff(c_2499, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2485])).
% 4.67/1.90  tff(c_2520, plain, (![B_16, A_15, A_123, A_126, C_17]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17)))))))), inference(superposition, [status(thm), theory('equality')], [c_2499, c_497])).
% 4.67/1.90  tff(c_2745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_2520])).
% 4.67/1.90  tff(c_2746, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2485])).
% 4.67/1.90  tff(c_2763, plain, (![B_16, A_15, A_123, A_126, C_17]: (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_123), k2_zfmisc_1(k1_tarski(A_126), k2_zfmisc_1(k2_tarski(A_15, B_16), k1_tarski(C_17)))))))), inference(superposition, [status(thm), theory('equality')], [c_2746, c_497])).
% 4.67/1.90  tff(c_2992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_2763])).
% 4.67/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.90  
% 4.67/1.90  Inference rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Ref     : 0
% 4.67/1.90  #Sup     : 1120
% 4.67/1.90  #Fact    : 0
% 4.67/1.90  #Define  : 0
% 4.67/1.90  #Split   : 3
% 4.67/1.90  #Chain   : 0
% 4.67/1.90  #Close   : 0
% 4.67/1.90  
% 4.67/1.90  Ordering : KBO
% 4.67/1.90  
% 4.67/1.90  Simplification rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Subsume      : 213
% 4.67/1.90  #Demod        : 382
% 4.67/1.90  #Tautology    : 130
% 4.67/1.90  #SimpNegUnit  : 0
% 4.67/1.90  #BackRed      : 4
% 4.67/1.90  
% 4.67/1.91  #Partial instantiations: 0
% 4.67/1.91  #Strategies tried      : 1
% 4.67/1.91  
% 4.67/1.91  Timing (in seconds)
% 4.67/1.91  ----------------------
% 4.67/1.91  Preprocessing        : 0.29
% 4.67/1.91  Parsing              : 0.15
% 4.67/1.91  CNF conversion       : 0.02
% 4.67/1.91  Main loop            : 0.85
% 4.67/1.91  Inferencing          : 0.32
% 4.67/1.91  Reduction            : 0.31
% 4.67/1.91  Demodulation         : 0.26
% 4.67/1.91  BG Simplification    : 0.04
% 4.67/1.91  Subsumption          : 0.14
% 4.67/1.91  Abstraction          : 0.06
% 4.67/1.91  MUC search           : 0.00
% 4.67/1.91  Cooper               : 0.00
% 4.67/1.91  Total                : 1.17
% 4.67/1.91  Index Insertion      : 0.00
% 4.67/1.91  Index Deletion       : 0.00
% 4.67/1.91  Index Matching       : 0.00
% 4.67/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
