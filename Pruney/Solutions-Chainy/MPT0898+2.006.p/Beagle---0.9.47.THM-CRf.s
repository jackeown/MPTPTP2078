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
% DateTime   : Thu Dec  3 10:09:50 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 411 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 834 expanded)
%              Number of equality atoms :  126 ( 828 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_47,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_3,B_4,C_5,C_31] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_31) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_107])).

tff(c_291,plain,(
    ! [A_3,B_4,C_5,C_31] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_31) = k4_zfmisc_1(A_3,B_4,C_5,C_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_28,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,(
    ! [A_32,B_33,C_34,D_35] : k2_zfmisc_1(k3_zfmisc_1(A_32,B_33,C_34),D_35) = k4_zfmisc_1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_403,plain,(
    ! [A_70,B_68,C_72,C_69,D_71] : k3_zfmisc_1(k3_zfmisc_1(A_70,B_68,C_69),D_71,C_72) = k2_zfmisc_1(k4_zfmisc_1(A_70,B_68,C_69,D_71),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_8])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != k1_xboole_0
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_746,plain,(
    ! [C_110,A_108,D_109,B_107,C_111] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_108,B_107,C_111,D_109),C_110) != k1_xboole_0
      | k1_xboole_0 = C_110
      | k1_xboole_0 = D_109
      | k3_zfmisc_1(A_108,B_107,C_111) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_12])).

tff(c_767,plain,(
    ! [C_110] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),C_110) != k1_xboole_0
      | k1_xboole_0 = C_110
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_746])).

tff(c_841,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_881,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_12])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [B_11,C_12] : k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_169,plain,(
    ! [B_11,C_12,D_35] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_35) = k2_zfmisc_1(k1_xboole_0,D_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_180,plain,(
    ! [B_11,C_12,D_35] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_898,plain,(
    ! [B_11,C_12,D_35] : k4_zfmisc_1('#skF_2',B_11,C_12,D_35) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_881,c_180])).

tff(c_1148,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,(
    ! [D_64,A_65,B_66,C_67] :
      ( k1_xboole_0 = D_64
      | k3_zfmisc_1(A_65,B_66,C_67) = k1_xboole_0
      | k4_zfmisc_1(A_65,B_66,C_67,D_64) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2])).

tff(c_393,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_378])).

tff(c_402,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_892,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_402])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_892])).

tff(c_1412,plain,(
    ! [C_110] :
      ( k1_xboole_0 = '#skF_2'
      | k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),C_110) != k1_xboole_0
      | k1_xboole_0 = C_110 ) ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_1415,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_1435,plain,(
    ! [B_11,C_12] : k3_zfmisc_1('#skF_2',B_11,C_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_1415,c_18])).

tff(c_1413,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_1416,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_1413])).

tff(c_1667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_1416])).

tff(c_1669,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_602,plain,(
    ! [E_91,A_92,D_89,F_88,B_90,C_93] :
      ( E_91 = B_90
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_90
      | k1_xboole_0 = A_92
      | k3_zfmisc_1(D_89,E_91,F_88) != k3_zfmisc_1(A_92,B_90,C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1695,plain,(
    ! [C_187,D_184,F_185,B_189,E_190,C_188,A_186] :
      ( E_190 = C_188
      | k1_xboole_0 = C_187
      | k1_xboole_0 = C_188
      | k2_zfmisc_1(A_186,B_189) = k1_xboole_0
      | k4_zfmisc_1(A_186,B_189,C_188,C_187) != k3_zfmisc_1(D_184,E_190,F_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_602])).

tff(c_1722,plain,(
    ! [E_190,D_184,F_185] :
      ( E_190 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_184,E_190,F_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1695])).

tff(c_1738,plain,(
    ! [E_190,D_184,F_185] :
      ( E_190 = '#skF_2'
      | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_184,E_190,F_185) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1669,c_1669,c_1722])).

tff(c_1739,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1738])).

tff(c_1752,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_2])).

tff(c_1761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1669,c_1669,c_1752])).

tff(c_1807,plain,(
    ! [E_199,D_200,F_201] :
      ( E_199 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k3_zfmisc_1(D_200,E_199,F_201) ) ),
    inference(splitRight,[status(thm)],[c_1738])).

tff(c_1813,plain,(
    ! [C_5,A_3,B_4,C_31] :
      ( C_5 = '#skF_2'
      | k4_zfmisc_1(A_3,B_4,C_5,C_31) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_1807])).

tff(c_1826,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1813])).

tff(c_1828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1826])).

tff(c_1829,plain,
    ( k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_1848,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1829])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_zfmisc_1(A_10,B_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1862,plain,(
    ! [A_10,B_11] : k3_zfmisc_1(A_10,B_11,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_14])).

tff(c_1830,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_156,plain,(
    ! [D_35,A_32,B_33,C_34] :
      ( k1_xboole_0 = D_35
      | k3_zfmisc_1(A_32,B_33,C_34) = k1_xboole_0
      | k4_zfmisc_1(A_32,B_33,C_34,D_35) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2])).

tff(c_1838,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_156])).

tff(c_2225,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_1838])).

tff(c_2226,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2225])).

tff(c_20,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] :
      ( F_18 = C_15
      | k1_xboole_0 = C_15
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1(A_13,B_14,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2060,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] :
      ( F_18 = C_15
      | C_15 = '#skF_2'
      | B_14 = '#skF_2'
      | A_13 = '#skF_2'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1(A_13,B_14,C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1848,c_1848,c_1848,c_20])).

tff(c_2236,plain,(
    ! [F_18,D_16,E_17] :
      ( F_18 = '#skF_1'
      | '#skF_2' = '#skF_1'
      | '#skF_2' = '#skF_1'
      | '#skF_2' = '#skF_1'
      | k3_zfmisc_1(D_16,E_17,F_18) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2226,c_2060])).

tff(c_2270,plain,(
    ! [F_240,D_241,E_242] :
      ( F_240 = '#skF_1'
      | k3_zfmisc_1(D_241,E_242,F_240) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_26,c_2236])).

tff(c_2285,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_2270])).

tff(c_2296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_2285])).

tff(c_2298,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1829])).

tff(c_2297,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1829])).

tff(c_2311,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2297,c_12])).

tff(c_2324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2298,c_2298,c_2298,c_2311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.77  
% 4.04/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.77  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.04/1.77  
% 4.04/1.77  %Foreground sorts:
% 4.04/1.77  
% 4.04/1.77  
% 4.04/1.77  %Background operators:
% 4.04/1.77  
% 4.04/1.77  
% 4.04/1.77  %Foreground operators:
% 4.04/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.77  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.04/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.04/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.04/1.77  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.04/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.04/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.77  
% 4.35/1.80  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 4.35/1.80  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.35/1.80  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.35/1.80  tff(f_47, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 4.35/1.80  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.35/1.80  tff(f_61, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 4.35/1.80  tff(c_26, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.35/1.80  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.35/1.80  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.80  tff(c_107, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.35/1.80  tff(c_123, plain, (![A_3, B_4, C_5, C_31]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_31)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_31))), inference(superposition, [status(thm), theory('equality')], [c_8, c_107])).
% 4.35/1.80  tff(c_291, plain, (![A_3, B_4, C_5, C_31]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_31)=k4_zfmisc_1(A_3, B_4, C_5, C_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_123])).
% 4.35/1.80  tff(c_28, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.35/1.80  tff(c_147, plain, (![A_32, B_33, C_34, D_35]: (k2_zfmisc_1(k3_zfmisc_1(A_32, B_33, C_34), D_35)=k4_zfmisc_1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.35/1.80  tff(c_403, plain, (![A_70, B_68, C_72, C_69, D_71]: (k3_zfmisc_1(k3_zfmisc_1(A_70, B_68, C_69), D_71, C_72)=k2_zfmisc_1(k4_zfmisc_1(A_70, B_68, C_69, D_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_147, c_8])).
% 4.35/1.80  tff(c_12, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!=k1_xboole_0 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.80  tff(c_746, plain, (![C_110, A_108, D_109, B_107, C_111]: (k2_zfmisc_1(k4_zfmisc_1(A_108, B_107, C_111, D_109), C_110)!=k1_xboole_0 | k1_xboole_0=C_110 | k1_xboole_0=D_109 | k3_zfmisc_1(A_108, B_107, C_111)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_403, c_12])).
% 4.35/1.80  tff(c_767, plain, (![C_110]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), C_110)!=k1_xboole_0 | k1_xboole_0=C_110 | k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_746])).
% 4.35/1.80  tff(c_841, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_767])).
% 4.35/1.80  tff(c_881, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_841, c_12])).
% 4.35/1.80  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.80  tff(c_18, plain, (![B_11, C_12]: (k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.80  tff(c_169, plain, (![B_11, C_12, D_35]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_35)=k2_zfmisc_1(k1_xboole_0, D_35))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 4.35/1.80  tff(c_180, plain, (![B_11, C_12, D_35]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_169])).
% 4.35/1.80  tff(c_898, plain, (![B_11, C_12, D_35]: (k4_zfmisc_1('#skF_2', B_11, C_12, D_35)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_881, c_881, c_180])).
% 4.35/1.80  tff(c_1148, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_898, c_28])).
% 4.35/1.80  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.35/1.80  tff(c_378, plain, (![D_64, A_65, B_66, C_67]: (k1_xboole_0=D_64 | k3_zfmisc_1(A_65, B_66, C_67)=k1_xboole_0 | k4_zfmisc_1(A_65, B_66, C_67, D_64)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_2])).
% 4.35/1.80  tff(c_393, plain, (k1_xboole_0='#skF_2' | k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_28, c_378])).
% 4.35/1.80  tff(c_402, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_393])).
% 4.35/1.80  tff(c_892, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_881, c_402])).
% 4.35/1.80  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1148, c_892])).
% 4.35/1.80  tff(c_1412, plain, (![C_110]: (k1_xboole_0='#skF_2' | k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), C_110)!=k1_xboole_0 | k1_xboole_0=C_110)), inference(splitRight, [status(thm)], [c_767])).
% 4.35/1.80  tff(c_1415, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1412])).
% 4.35/1.80  tff(c_1435, plain, (![B_11, C_12]: (k3_zfmisc_1('#skF_2', B_11, C_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_1415, c_18])).
% 4.35/1.80  tff(c_1413, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_767])).
% 4.35/1.80  tff(c_1416, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_1413])).
% 4.35/1.80  tff(c_1667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1435, c_1416])).
% 4.35/1.80  tff(c_1669, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1412])).
% 4.35/1.80  tff(c_602, plain, (![E_91, A_92, D_89, F_88, B_90, C_93]: (E_91=B_90 | k1_xboole_0=C_93 | k1_xboole_0=B_90 | k1_xboole_0=A_92 | k3_zfmisc_1(D_89, E_91, F_88)!=k3_zfmisc_1(A_92, B_90, C_93))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.35/1.80  tff(c_1695, plain, (![C_187, D_184, F_185, B_189, E_190, C_188, A_186]: (E_190=C_188 | k1_xboole_0=C_187 | k1_xboole_0=C_188 | k2_zfmisc_1(A_186, B_189)=k1_xboole_0 | k4_zfmisc_1(A_186, B_189, C_188, C_187)!=k3_zfmisc_1(D_184, E_190, F_185))), inference(superposition, [status(thm), theory('equality')], [c_291, c_602])).
% 4.35/1.80  tff(c_1722, plain, (![E_190, D_184, F_185]: (E_190='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_184, E_190, F_185))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1695])).
% 4.35/1.80  tff(c_1738, plain, (![E_190, D_184, F_185]: (E_190='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_184, E_190, F_185))), inference(negUnitSimplification, [status(thm)], [c_1669, c_1669, c_1722])).
% 4.35/1.80  tff(c_1739, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1738])).
% 4.35/1.80  tff(c_1752, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1739, c_2])).
% 4.35/1.80  tff(c_1761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1669, c_1669, c_1752])).
% 4.35/1.80  tff(c_1807, plain, (![E_199, D_200, F_201]: (E_199='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k3_zfmisc_1(D_200, E_199, F_201))), inference(splitRight, [status(thm)], [c_1738])).
% 4.35/1.80  tff(c_1813, plain, (![C_5, A_3, B_4, C_31]: (C_5='#skF_2' | k4_zfmisc_1(A_3, B_4, C_5, C_31)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_1807])).
% 4.35/1.80  tff(c_1826, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_1813])).
% 4.35/1.80  tff(c_1828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1826])).
% 4.35/1.80  tff(c_1829, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_393])).
% 4.35/1.80  tff(c_1848, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1829])).
% 4.35/1.80  tff(c_14, plain, (![A_10, B_11]: (k3_zfmisc_1(A_10, B_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.35/1.80  tff(c_1862, plain, (![A_10, B_11]: (k3_zfmisc_1(A_10, B_11, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_14])).
% 4.35/1.80  tff(c_1830, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_393])).
% 4.35/1.80  tff(c_156, plain, (![D_35, A_32, B_33, C_34]: (k1_xboole_0=D_35 | k3_zfmisc_1(A_32, B_33, C_34)=k1_xboole_0 | k4_zfmisc_1(A_32, B_33, C_34, D_35)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_2])).
% 4.35/1.80  tff(c_1838, plain, (k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1830, c_156])).
% 4.35/1.80  tff(c_2225, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_1838])).
% 4.35/1.80  tff(c_2226, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_26, c_2225])).
% 4.35/1.80  tff(c_20, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (F_18=C_15 | k1_xboole_0=C_15 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.35/1.80  tff(c_2060, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (F_18=C_15 | C_15='#skF_2' | B_14='#skF_2' | A_13='#skF_2' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1(A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_1848, c_1848, c_1848, c_20])).
% 4.35/1.80  tff(c_2236, plain, (![F_18, D_16, E_17]: (F_18='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | k3_zfmisc_1(D_16, E_17, F_18)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2226, c_2060])).
% 4.35/1.80  tff(c_2270, plain, (![F_240, D_241, E_242]: (F_240='#skF_1' | k3_zfmisc_1(D_241, E_242, F_240)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_26, c_2236])).
% 4.35/1.80  tff(c_2285, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1862, c_2270])).
% 4.35/1.80  tff(c_2296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_2285])).
% 4.35/1.80  tff(c_2298, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1829])).
% 4.35/1.80  tff(c_2297, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1829])).
% 4.35/1.80  tff(c_2311, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2297, c_12])).
% 4.35/1.80  tff(c_2324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2298, c_2298, c_2298, c_2311])).
% 4.35/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.80  
% 4.35/1.80  Inference rules
% 4.35/1.80  ----------------------
% 4.35/1.80  #Ref     : 6
% 4.35/1.80  #Sup     : 570
% 4.35/1.80  #Fact    : 0
% 4.35/1.80  #Define  : 0
% 4.35/1.80  #Split   : 6
% 4.35/1.80  #Chain   : 0
% 4.35/1.80  #Close   : 0
% 4.35/1.80  
% 4.35/1.80  Ordering : KBO
% 4.35/1.80  
% 4.35/1.80  Simplification rules
% 4.35/1.80  ----------------------
% 4.35/1.80  #Subsume      : 54
% 4.35/1.80  #Demod        : 412
% 4.35/1.80  #Tautology    : 340
% 4.35/1.80  #SimpNegUnit  : 14
% 4.35/1.80  #BackRed      : 65
% 4.35/1.80  
% 4.35/1.80  #Partial instantiations: 0
% 4.35/1.80  #Strategies tried      : 1
% 4.35/1.80  
% 4.35/1.80  Timing (in seconds)
% 4.35/1.80  ----------------------
% 4.42/1.80  Preprocessing        : 0.36
% 4.42/1.80  Parsing              : 0.18
% 4.42/1.80  CNF conversion       : 0.02
% 4.42/1.80  Main loop            : 0.67
% 4.42/1.80  Inferencing          : 0.24
% 4.42/1.80  Reduction            : 0.18
% 4.42/1.80  Demodulation         : 0.13
% 4.42/1.80  BG Simplification    : 0.03
% 4.42/1.80  Subsumption          : 0.17
% 4.42/1.80  Abstraction          : 0.04
% 4.42/1.80  MUC search           : 0.00
% 4.42/1.80  Cooper               : 0.00
% 4.42/1.80  Total                : 1.08
% 4.42/1.80  Index Insertion      : 0.00
% 4.42/1.80  Index Deletion       : 0.00
% 4.42/1.80  Index Matching       : 0.00
% 4.42/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
