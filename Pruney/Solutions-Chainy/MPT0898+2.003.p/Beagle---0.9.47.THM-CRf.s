%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 379 expanded)
%              Number of leaves         :   15 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 791 expanded)
%              Number of equality atoms :  109 ( 785 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12,D_13] : k2_zfmisc_1(k3_zfmisc_1(A_10,B_11,C_12),D_13) = k4_zfmisc_1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_324,plain,(
    ! [D_56,B_57,A_58,C_59] :
      ( D_56 = B_57
      | k1_xboole_0 = B_57
      | k1_xboole_0 = A_58
      | k2_zfmisc_1(C_59,D_56) != k2_zfmisc_1(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_724,plain,(
    ! [C_110,D_108,C_109,A_107,B_105,D_106] :
      ( D_108 = D_106
      | k1_xboole_0 = D_108
      | k3_zfmisc_1(A_107,B_105,C_109) = k1_xboole_0
      | k4_zfmisc_1(A_107,B_105,C_109,D_108) != k2_zfmisc_1(C_110,D_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_324])).

tff(c_745,plain,(
    ! [D_106,C_110] :
      ( D_106 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_110,D_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_724])).

tff(c_874,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_745])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k3_zfmisc_1(A_14,B_15,C_16) != k1_xboole_0
      | k1_xboole_0 = C_16
      | k1_xboole_0 = B_15
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_912,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_16])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_14,C_16] : k3_zfmisc_1(A_14,k1_xboole_0,C_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_zfmisc_1(k3_zfmisc_1(A_33,B_34,C_35),D_36) = k4_zfmisc_1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_186,plain,(
    ! [A_14,C_16,D_36] : k4_zfmisc_1(A_14,k1_xboole_0,C_16,D_36) = k2_zfmisc_1(k1_xboole_0,D_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_161])).

tff(c_195,plain,(
    ! [A_14,C_16,D_36] : k4_zfmisc_1(A_14,k1_xboole_0,C_16,D_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_186])).

tff(c_928,plain,(
    ! [A_14,C_16,D_36] : k4_zfmisc_1(A_14,'#skF_2',C_16,D_36) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_912,c_195])).

tff(c_1160,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,(
    ! [D_64,A_65,B_66,C_67] :
      ( k1_xboole_0 = D_64
      | k3_zfmisc_1(A_65,B_66,C_67) = k1_xboole_0
      | k4_zfmisc_1(A_65,B_66,C_67,D_64) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_421,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_406])).

tff(c_457,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_922,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_457])).

tff(c_1363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_922])).

tff(c_1364,plain,(
    ! [D_106,C_110] :
      ( k1_xboole_0 = '#skF_2'
      | D_106 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_110,D_106) ) ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_1366,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1364])).

tff(c_22,plain,(
    ! [B_15,C_16] : k3_zfmisc_1(k1_xboole_0,B_15,C_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1421,plain,(
    ! [B_15,C_16] : k3_zfmisc_1('#skF_2',B_15,C_16) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1366,c_22])).

tff(c_1365,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_745])).

tff(c_1401,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1365])).

tff(c_1615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_1401])).

tff(c_1651,plain,(
    ! [D_178,C_179] :
      ( D_178 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_179,D_178) ) ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_1654,plain,(
    ! [D_13,A_10,B_11,C_12] :
      ( D_13 = '#skF_2'
      | k4_zfmisc_1(A_10,B_11,C_12,D_13) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1651])).

tff(c_1684,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1654])).

tff(c_1686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1684])).

tff(c_1687,plain,
    ( k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_1706,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1687])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1723,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1706,c_4])).

tff(c_1688,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_170,plain,(
    ! [D_36,A_33,B_34,C_35] :
      ( k1_xboole_0 = D_36
      | k3_zfmisc_1(A_33,B_34,C_35) = k1_xboole_0
      | k4_zfmisc_1(A_33,B_34,C_35,D_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_1696,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_170])).

tff(c_2073,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1706,c_1696])).

tff(c_2074,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2073])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_336,plain,(
    ! [D_56,A_7,B_8,C_9,C_59] :
      ( D_56 = C_9
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k2_zfmisc_1(C_59,D_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_324])).

tff(c_2130,plain,(
    ! [C_226,B_222,A_224,D_225,C_223] :
      ( D_225 = C_223
      | C_223 = '#skF_2'
      | k2_zfmisc_1(A_224,B_222) = '#skF_2'
      | k3_zfmisc_1(A_224,B_222,C_223) != k2_zfmisc_1(C_226,D_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1706,c_336])).

tff(c_2133,plain,(
    ! [D_225,C_226] :
      ( D_225 = '#skF_1'
      | '#skF_2' = '#skF_1'
      | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
      | k2_zfmisc_1(C_226,D_225) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2074,c_2130])).

tff(c_2161,plain,(
    ! [D_225,C_226] :
      ( D_225 = '#skF_1'
      | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
      | k2_zfmisc_1(C_226,D_225) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2133])).

tff(c_2170,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2161])).

tff(c_1719,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_2'
      | A_1 = '#skF_2'
      | k2_zfmisc_1(A_1,B_2) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1706,c_1706,c_2])).

tff(c_2174,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2170,c_1719])).

tff(c_2186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_2174])).

tff(c_2189,plain,(
    ! [D_227,C_228] :
      ( D_227 = '#skF_1'
      | k2_zfmisc_1(C_228,D_227) != '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_2161])).

tff(c_2195,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_2189])).

tff(c_2206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2195])).

tff(c_2208,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1687])).

tff(c_2207,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1687])).

tff(c_2221,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2207,c_16])).

tff(c_2231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2208,c_2208,c_2208,c_2221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.60  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.44/1.60  
% 3.44/1.60  %Foreground sorts:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Background operators:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Foreground operators:
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.60  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.44/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.60  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.60  
% 3.44/1.61  tff(f_62, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 3.44/1.61  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.44/1.61  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.44/1.61  tff(f_57, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.44/1.61  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.44/1.61  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.44/1.61  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.61  tff(c_14, plain, (![A_10, B_11, C_12, D_13]: (k2_zfmisc_1(k3_zfmisc_1(A_10, B_11, C_12), D_13)=k4_zfmisc_1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.61  tff(c_26, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.61  tff(c_324, plain, (![D_56, B_57, A_58, C_59]: (D_56=B_57 | k1_xboole_0=B_57 | k1_xboole_0=A_58 | k2_zfmisc_1(C_59, D_56)!=k2_zfmisc_1(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.61  tff(c_724, plain, (![C_110, D_108, C_109, A_107, B_105, D_106]: (D_108=D_106 | k1_xboole_0=D_108 | k3_zfmisc_1(A_107, B_105, C_109)=k1_xboole_0 | k4_zfmisc_1(A_107, B_105, C_109, D_108)!=k2_zfmisc_1(C_110, D_106))), inference(superposition, [status(thm), theory('equality')], [c_14, c_324])).
% 3.44/1.61  tff(c_745, plain, (![D_106, C_110]: (D_106='#skF_2' | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_110, D_106))), inference(superposition, [status(thm), theory('equality')], [c_26, c_724])).
% 3.44/1.61  tff(c_874, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_745])).
% 3.44/1.61  tff(c_16, plain, (![A_14, B_15, C_16]: (k3_zfmisc_1(A_14, B_15, C_16)!=k1_xboole_0 | k1_xboole_0=C_16 | k1_xboole_0=B_15 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.61  tff(c_912, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_874, c_16])).
% 3.44/1.61  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.61  tff(c_20, plain, (![A_14, C_16]: (k3_zfmisc_1(A_14, k1_xboole_0, C_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.61  tff(c_161, plain, (![A_33, B_34, C_35, D_36]: (k2_zfmisc_1(k3_zfmisc_1(A_33, B_34, C_35), D_36)=k4_zfmisc_1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.61  tff(c_186, plain, (![A_14, C_16, D_36]: (k4_zfmisc_1(A_14, k1_xboole_0, C_16, D_36)=k2_zfmisc_1(k1_xboole_0, D_36))), inference(superposition, [status(thm), theory('equality')], [c_20, c_161])).
% 3.44/1.61  tff(c_195, plain, (![A_14, C_16, D_36]: (k4_zfmisc_1(A_14, k1_xboole_0, C_16, D_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_186])).
% 3.44/1.61  tff(c_928, plain, (![A_14, C_16, D_36]: (k4_zfmisc_1(A_14, '#skF_2', C_16, D_36)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_912, c_912, c_195])).
% 3.44/1.61  tff(c_1160, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_928, c_26])).
% 3.44/1.61  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.61  tff(c_406, plain, (![D_64, A_65, B_66, C_67]: (k1_xboole_0=D_64 | k3_zfmisc_1(A_65, B_66, C_67)=k1_xboole_0 | k4_zfmisc_1(A_65, B_66, C_67, D_64)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 3.44/1.61  tff(c_421, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_406])).
% 3.44/1.61  tff(c_457, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_421])).
% 3.44/1.61  tff(c_922, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_912, c_457])).
% 3.44/1.61  tff(c_1363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1160, c_922])).
% 3.44/1.61  tff(c_1364, plain, (![D_106, C_110]: (k1_xboole_0='#skF_2' | D_106='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_110, D_106))), inference(splitRight, [status(thm)], [c_745])).
% 3.44/1.61  tff(c_1366, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1364])).
% 3.44/1.61  tff(c_22, plain, (![B_15, C_16]: (k3_zfmisc_1(k1_xboole_0, B_15, C_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.61  tff(c_1421, plain, (![B_15, C_16]: (k3_zfmisc_1('#skF_2', B_15, C_16)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1366, c_22])).
% 3.44/1.61  tff(c_1365, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_745])).
% 3.44/1.61  tff(c_1401, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1365])).
% 3.44/1.61  tff(c_1615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1421, c_1401])).
% 3.44/1.61  tff(c_1651, plain, (![D_178, C_179]: (D_178='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_179, D_178))), inference(splitRight, [status(thm)], [c_1364])).
% 3.44/1.61  tff(c_1654, plain, (![D_13, A_10, B_11, C_12]: (D_13='#skF_2' | k4_zfmisc_1(A_10, B_11, C_12, D_13)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1651])).
% 3.44/1.61  tff(c_1684, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1654])).
% 3.44/1.61  tff(c_1686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1684])).
% 3.44/1.61  tff(c_1687, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_421])).
% 3.44/1.61  tff(c_1706, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1687])).
% 3.44/1.61  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.61  tff(c_1723, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1706, c_4])).
% 3.44/1.61  tff(c_1688, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_421])).
% 3.44/1.61  tff(c_170, plain, (![D_36, A_33, B_34, C_35]: (k1_xboole_0=D_36 | k3_zfmisc_1(A_33, B_34, C_35)=k1_xboole_0 | k4_zfmisc_1(A_33, B_34, C_35, D_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 3.44/1.61  tff(c_1696, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1688, c_170])).
% 3.44/1.61  tff(c_2073, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1706, c_1696])).
% 3.44/1.61  tff(c_2074, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24, c_2073])).
% 3.44/1.61  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.61  tff(c_336, plain, (![D_56, A_7, B_8, C_9, C_59]: (D_56=C_9 | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k2_zfmisc_1(C_59, D_56))), inference(superposition, [status(thm), theory('equality')], [c_12, c_324])).
% 3.44/1.61  tff(c_2130, plain, (![C_226, B_222, A_224, D_225, C_223]: (D_225=C_223 | C_223='#skF_2' | k2_zfmisc_1(A_224, B_222)='#skF_2' | k3_zfmisc_1(A_224, B_222, C_223)!=k2_zfmisc_1(C_226, D_225))), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1706, c_336])).
% 3.44/1.61  tff(c_2133, plain, (![D_225, C_226]: (D_225='#skF_1' | '#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | k2_zfmisc_1(C_226, D_225)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2074, c_2130])).
% 3.44/1.61  tff(c_2161, plain, (![D_225, C_226]: (D_225='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | k2_zfmisc_1(C_226, D_225)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_2133])).
% 3.44/1.61  tff(c_2170, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitLeft, [status(thm)], [c_2161])).
% 3.44/1.61  tff(c_1719, plain, (![B_2, A_1]: (B_2='#skF_2' | A_1='#skF_2' | k2_zfmisc_1(A_1, B_2)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1706, c_1706, c_2])).
% 3.44/1.61  tff(c_2174, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2170, c_1719])).
% 3.44/1.61  tff(c_2186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_2174])).
% 3.44/1.61  tff(c_2189, plain, (![D_227, C_228]: (D_227='#skF_1' | k2_zfmisc_1(C_228, D_227)!='#skF_2')), inference(splitRight, [status(thm)], [c_2161])).
% 3.44/1.61  tff(c_2195, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1723, c_2189])).
% 3.44/1.61  tff(c_2206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2195])).
% 3.44/1.61  tff(c_2208, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1687])).
% 3.44/1.61  tff(c_2207, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1687])).
% 3.44/1.61  tff(c_2221, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2207, c_16])).
% 3.44/1.61  tff(c_2231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2208, c_2208, c_2208, c_2221])).
% 3.44/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  Inference rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Ref     : 4
% 3.44/1.61  #Sup     : 548
% 3.44/1.61  #Fact    : 0
% 3.44/1.61  #Define  : 0
% 3.44/1.61  #Split   : 5
% 3.44/1.61  #Chain   : 0
% 3.44/1.61  #Close   : 0
% 3.44/1.61  
% 3.44/1.61  Ordering : KBO
% 3.44/1.61  
% 3.44/1.61  Simplification rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Subsume      : 57
% 3.44/1.61  #Demod        : 399
% 3.44/1.61  #Tautology    : 318
% 3.44/1.61  #SimpNegUnit  : 9
% 3.44/1.61  #BackRed      : 72
% 3.44/1.61  
% 3.44/1.61  #Partial instantiations: 0
% 3.44/1.61  #Strategies tried      : 1
% 3.44/1.61  
% 3.44/1.61  Timing (in seconds)
% 3.44/1.61  ----------------------
% 3.44/1.62  Preprocessing        : 0.27
% 3.44/1.62  Parsing              : 0.14
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.53
% 3.44/1.62  Inferencing          : 0.20
% 3.44/1.62  Reduction            : 0.15
% 3.44/1.62  Demodulation         : 0.11
% 3.44/1.62  BG Simplification    : 0.03
% 3.44/1.62  Subsumption          : 0.12
% 3.44/1.62  Abstraction          : 0.03
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.83
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
