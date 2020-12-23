%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:46 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :  368 (9655 expanded)
%              Number of leaves         :   22 (2941 expanded)
%              Depth                    :   29
%              Number of atoms          :  550 (28199 expanded)
%              Number of equality atoms :  516 (28165 expanded)
%              Maximal formula depth    :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_26,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_191,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_zfmisc_1(k3_zfmisc_1(A_29,B_30,C_31),D_32) = k4_zfmisc_1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_527,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k2_relat_1(k4_zfmisc_1(A_67,B_68,C_69,D_70)) = D_70
      | k1_xboole_0 = D_70
      | k3_zfmisc_1(A_67,B_68,C_69) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_548,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_527])).

tff(c_651,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_85,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_xboole_0 = C_20
      | k2_zfmisc_1(A_18,B_19) = k1_xboole_0
      | k3_zfmisc_1(A_18,B_19,C_20) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_672,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_97])).

tff(c_676,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_701,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_2])).

tff(c_703,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_405,plain,(
    ! [D_55,A_56,B_57,C_58] :
      ( k1_xboole_0 = D_55
      | k3_zfmisc_1(A_56,B_57,C_58) = k1_xboole_0
      | k4_zfmisc_1(A_56,B_57,C_58,D_55) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_420,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_405])).

tff(c_429,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_784,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_429])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_668,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_14])).

tff(c_673,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_668])).

tff(c_983,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_673])).

tff(c_984,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_26])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_784,c_984])).

tff(c_987,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_1070,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_429])).

tff(c_1298,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_673])).

tff(c_1299,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_26])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_1299])).

tff(c_1302,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_1308,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1302,c_429])).

tff(c_1540,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1302,c_673])).

tff(c_1541,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_26])).

tff(c_1543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1308,c_1541])).

tff(c_1545,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k1_relat_1(k2_zfmisc_1(A_3,B_4)) = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_556,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k1_relat_1(k4_zfmisc_1(A_71,B_72,C_73,D_74)) = k3_zfmisc_1(A_71,B_72,C_73)
      | k1_xboole_0 = D_74
      | k3_zfmisc_1(A_71,B_72,C_73) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_10])).

tff(c_577,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_556])).

tff(c_1546,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1545,c_577])).

tff(c_1547,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1546])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_4])).

tff(c_1559,plain,(
    ! [A_29,B_30,C_31] : k4_zfmisc_1(A_29,B_30,C_31,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1547,c_210])).

tff(c_1803,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_26])).

tff(c_1552,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_429])).

tff(c_1850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_1552])).

tff(c_1852,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_1544,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_1853,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1852,c_1544])).

tff(c_197,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k2_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = D_32
      | k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_1857,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1853,c_197])).

tff(c_1863,plain,
    ( '#skF_8' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1857])).

tff(c_1866,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1863])).

tff(c_1879,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_97])).

tff(c_1890,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1879])).

tff(c_1925,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1890,c_2])).

tff(c_1936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_1925])).

tff(c_1938,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1863])).

tff(c_1851,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1546])).

tff(c_203,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( k1_relat_1(k4_zfmisc_1(A_29,B_30,C_31,D_32)) = k3_zfmisc_1(A_29,B_30,C_31)
      | k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_10])).

tff(c_1965,plain,
    ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1851,c_203])).

tff(c_1971,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1938,c_18,c_1965])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k2_zfmisc_1(A_25,B_26)) = B_26
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_1985,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_157])).

tff(c_2142,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1985])).

tff(c_2167,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_2])).

tff(c_2169,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2167])).

tff(c_2171,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_1938])).

tff(c_117,plain,(
    ! [B_2,C_20] : k3_zfmisc_1(k1_xboole_0,B_2,C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_121,plain,(
    ! [B_2,C_20] : k3_zfmisc_1(k1_xboole_0,B_2,C_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_117])).

tff(c_2183,plain,(
    ! [B_2,C_20] : k3_zfmisc_1('#skF_5',B_2,C_20) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_2169,c_121])).

tff(c_2293,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_1971])).

tff(c_2295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2171,c_2293])).

tff(c_2296,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2167])).

tff(c_2301,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2296,c_1938])).

tff(c_2155,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_12])).

tff(c_2166,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2155])).

tff(c_2389,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2296,c_2166])).

tff(c_2390,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_1971])).

tff(c_2451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2301,c_2390])).

tff(c_2452,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1985])).

tff(c_2454,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2452])).

tff(c_2458,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_157])).

tff(c_2464,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2458])).

tff(c_2467,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2464])).

tff(c_2486,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_2])).

tff(c_2497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_2486])).

tff(c_2499,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2464])).

tff(c_2453,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1985])).

tff(c_2498,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2464])).

tff(c_2503,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_1971])).

tff(c_94,plain,(
    ! [A_18,B_19,C_20] :
      ( k1_relat_1(k3_zfmisc_1(A_18,B_19,C_20)) = k2_zfmisc_1(A_18,B_19)
      | k1_xboole_0 = C_20
      | k2_zfmisc_1(A_18,B_19) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_10])).

tff(c_2516,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2503,c_94])).

tff(c_2532,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2453,c_20,c_2516])).

tff(c_2563,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2532,c_94])).

tff(c_2569,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2499,c_20,c_2563])).

tff(c_2583,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_8])).

tff(c_2661,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2583])).

tff(c_2663,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_2499])).

tff(c_2683,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_2661,c_6])).

tff(c_2725,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_2569])).

tff(c_2727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2663,c_2725])).

tff(c_2729,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2583])).

tff(c_2589,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2569,c_10])).

tff(c_2730,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2729,c_2589])).

tff(c_2731,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2730])).

tff(c_2734,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_2499])).

tff(c_2753,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_2731,c_4])).

tff(c_2783,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_2569])).

tff(c_2785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2734,c_2783])).

tff(c_2786,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2730])).

tff(c_2791,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2786,c_10])).

tff(c_2798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_60,c_2791])).

tff(c_2799,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2452])).

tff(c_2802,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2799,c_1938])).

tff(c_101,plain,(
    ! [A_18,B_19] : k3_zfmisc_1(A_18,B_19,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_2817,plain,(
    ! [A_18,B_19] : k3_zfmisc_1(A_18,B_19,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2799,c_2799,c_101])).

tff(c_2951,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2817,c_1971])).

tff(c_2953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2802,c_2951])).

tff(c_2955,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_206,plain,(
    ! [D_32,A_29,B_30,C_31] :
      ( k1_xboole_0 = D_32
      | k3_zfmisc_1(A_29,B_30,C_31) = k1_xboole_0
      | k4_zfmisc_1(A_29,B_30,C_31,D_32) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_2])).

tff(c_2960,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2955,c_206])).

tff(c_2965,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2960])).

tff(c_2973,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2965,c_97])).

tff(c_2982,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2973])).

tff(c_3000,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2982,c_2])).

tff(c_3010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_3000])).

tff(c_3011,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_3017,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3012,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_3120,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_26])).

tff(c_3149,plain,(
    ! [A_182,B_183,C_184,D_185] : k2_zfmisc_1(k3_zfmisc_1(A_182,B_183,C_184),D_185) = k4_zfmisc_1(A_182,B_183,C_184,D_185) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3391,plain,(
    ! [A_212,B_213,C_214,D_215] :
      ( k2_relat_1(k4_zfmisc_1(A_212,B_213,C_214,D_215)) = D_215
      | k1_xboole_0 = D_215
      | k3_zfmisc_1(A_212,B_213,C_214) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_8])).

tff(c_3412,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8'
    | k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3120,c_3391])).

tff(c_3513,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3412])).

tff(c_3038,plain,(
    ! [A_171,B_172,C_173] : k2_zfmisc_1(k2_zfmisc_1(A_171,B_172),C_173) = k3_zfmisc_1(A_171,B_172,C_173) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3050,plain,(
    ! [C_173,A_171,B_172] :
      ( k1_xboole_0 = C_173
      | k2_zfmisc_1(A_171,B_172) = k1_xboole_0
      | k3_zfmisc_1(A_171,B_172,C_173) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3038,c_2])).

tff(c_3533,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3513,c_3050])).

tff(c_3536,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3533])).

tff(c_3552,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3536,c_2])).

tff(c_3561,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3552])).

tff(c_3529,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_3513,c_14])).

tff(c_3534,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3529])).

tff(c_3808,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3561,c_3534])).

tff(c_3809,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3808,c_3120])).

tff(c_3363,plain,(
    ! [D_208,A_209,B_210,C_211] :
      ( k1_xboole_0 = D_208
      | k3_zfmisc_1(A_209,B_210,C_211) = k1_xboole_0
      | k4_zfmisc_1(A_209,B_210,C_211,D_208) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_2])).

tff(c_3378,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3120,c_3363])).

tff(c_3387,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3378])).

tff(c_3566,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3561,c_3387])).

tff(c_4040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3809,c_3566])).

tff(c_4041,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3533])).

tff(c_4045,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_3387])).

tff(c_4282,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_3534])).

tff(c_4283,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4282,c_3120])).

tff(c_4285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4045,c_4283])).

tff(c_4286,plain,
    ( k1_xboole_0 = '#skF_8'
    | k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_4318,plain,(
    k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4286])).

tff(c_3161,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relat_1(k4_zfmisc_1(A_182,B_183,C_184,D_185)) = D_185
      | k1_xboole_0 = D_185
      | k3_zfmisc_1(A_182,B_183,C_184) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_8])).

tff(c_4322,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4318,c_3161])).

tff(c_4328,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_3017,c_4322])).

tff(c_4343,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4328,c_3050])).

tff(c_4354,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_4343])).

tff(c_4372,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4354,c_2])).

tff(c_4382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_4372])).

tff(c_4383,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4286])).

tff(c_4388,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_3387])).

tff(c_3168,plain,(
    ! [A_182,B_183,C_184] : k4_zfmisc_1(A_182,B_183,C_184,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_4])).

tff(c_4396,plain,(
    ! [A_182,B_183,C_184] : k4_zfmisc_1(A_182,B_183,C_184,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_4383,c_3168])).

tff(c_4576,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_3120])).

tff(c_4646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4388,c_4576])).

tff(c_4648,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3378])).

tff(c_3164,plain,(
    ! [D_185,A_182,B_183,C_184] :
      ( k1_xboole_0 = D_185
      | k3_zfmisc_1(A_182,B_183,C_184) = k1_xboole_0
      | k4_zfmisc_1(A_182,B_183,C_184,D_185) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3149,c_2])).

tff(c_4653,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_3164])).

tff(c_4658,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_4653])).

tff(c_4666,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4658,c_3050])).

tff(c_4675,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_4666])).

tff(c_4693,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4675,c_2])).

tff(c_4703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_4693])).

tff(c_4704,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_4710,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4704])).

tff(c_4705,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_4791,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_3012,c_26])).

tff(c_4842,plain,(
    ! [A_315,B_316,C_317,D_318] : k2_zfmisc_1(k3_zfmisc_1(A_315,B_316,C_317),D_318) = k4_zfmisc_1(A_315,B_316,C_317,D_318) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5149,plain,(
    ! [A_350,B_351,C_352,D_353] :
      ( k2_relat_1(k4_zfmisc_1(A_350,B_351,C_352,D_353)) = D_353
      | k1_xboole_0 = D_353
      | k3_zfmisc_1(A_350,B_351,C_352) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_8])).

tff(c_5170,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4791,c_5149])).

tff(c_5177,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_5170])).

tff(c_5178,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5177])).

tff(c_4751,plain,(
    ! [A_306,B_307,C_308] : k2_zfmisc_1(k2_zfmisc_1(A_306,B_307),C_308) = k3_zfmisc_1(A_306,B_307,C_308) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4766,plain,(
    ! [C_308,A_306,B_307] :
      ( k1_xboole_0 = C_308
      | k2_zfmisc_1(A_306,B_307) = k1_xboole_0
      | k3_zfmisc_1(A_306,B_307,C_308) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_2])).

tff(c_5195,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5178,c_4766])).

tff(c_5198,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5195])).

tff(c_5214,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5198,c_2])).

tff(c_5223,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_5214])).

tff(c_5191,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_5178,c_14])).

tff(c_5196,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5191])).

tff(c_5496,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_5196])).

tff(c_5497,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5496,c_4791])).

tff(c_5056,plain,(
    ! [D_341,A_342,B_343,C_344] :
      ( k1_xboole_0 = D_341
      | k3_zfmisc_1(A_342,B_343,C_344) = k1_xboole_0
      | k4_zfmisc_1(A_342,B_343,C_344,D_341) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_2])).

tff(c_5071,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4791,c_5056])).

tff(c_5080,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_5071])).

tff(c_5145,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5080])).

tff(c_5228,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5223,c_5145])).

tff(c_5705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5497,c_5228])).

tff(c_5706,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5195])).

tff(c_5710,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5706,c_5145])).

tff(c_5954,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5706,c_5196])).

tff(c_5955,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5954,c_4791])).

tff(c_5957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5710,c_5955])).

tff(c_5959,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5177])).

tff(c_6005,plain,(
    ! [A_408,B_409,C_410,D_411] :
      ( k1_relat_1(k4_zfmisc_1(A_408,B_409,C_410,D_411)) = k3_zfmisc_1(A_408,B_409,C_410)
      | k1_xboole_0 = D_411
      | k3_zfmisc_1(A_408,B_409,C_410) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_10])).

tff(c_6026,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4791,c_6005])).

tff(c_6033,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_5959,c_18,c_6026])).

tff(c_4851,plain,(
    ! [A_315,B_316,C_317,D_318] :
      ( k1_relat_1(k4_zfmisc_1(A_315,B_316,C_317,D_318)) = k3_zfmisc_1(A_315,B_316,C_317)
      | k1_xboole_0 = D_318
      | k3_zfmisc_1(A_315,B_316,C_317) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_10])).

tff(c_6037,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6033,c_4851])).

tff(c_6043,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_6037])).

tff(c_6046,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6043])).

tff(c_6059,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6046,c_4766])).

tff(c_6070,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_6059])).

tff(c_6088,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6070,c_2])).

tff(c_6098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_6088])).

tff(c_6099,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_6043])).

tff(c_4763,plain,(
    ! [A_306,B_307,C_308] :
      ( k2_relat_1(k3_zfmisc_1(A_306,B_307,C_308)) = C_308
      | k1_xboole_0 = C_308
      | k2_zfmisc_1(A_306,B_307) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_8])).

tff(c_6112,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6099,c_4763])).

tff(c_6283,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6112])).

tff(c_6302,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6283,c_2])).

tff(c_6312,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_6302])).

tff(c_6100,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6043])).

tff(c_6317,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6312,c_6100])).

tff(c_6293,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_6283,c_12])).

tff(c_6307,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6293])).

tff(c_6422,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6312,c_6307])).

tff(c_6423,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6422,c_6099])).

tff(c_6425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6317,c_6423])).

tff(c_6426,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6112])).

tff(c_6428,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6426])).

tff(c_6432,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6428,c_4763])).

tff(c_6438,plain,
    ( '#skF_7' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_6432])).

tff(c_6442,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6438])).

tff(c_6461,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6442,c_2])).

tff(c_6472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_6461])).

tff(c_6474,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6438])).

tff(c_6427,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6112])).

tff(c_6473,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6438])).

tff(c_6477,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6473,c_6099])).

tff(c_4760,plain,(
    ! [A_306,B_307,C_308] :
      ( k1_relat_1(k3_zfmisc_1(A_306,B_307,C_308)) = k2_zfmisc_1(A_306,B_307)
      | k1_xboole_0 = C_308
      | k2_zfmisc_1(A_306,B_307) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_10])).

tff(c_6500,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6477,c_4760])).

tff(c_6515,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_6427,c_20,c_6500])).

tff(c_6525,plain,
    ( k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6515,c_4760])).

tff(c_6531,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_6474,c_20,c_6525])).

tff(c_6551,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6531,c_8])).

tff(c_6561,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_6551])).

tff(c_6565,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6561])).

tff(c_6566,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_6474])).

tff(c_6587,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_6565,c_4])).

tff(c_6597,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6587,c_6531])).

tff(c_6676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6566,c_6597])).

tff(c_6677,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6561])).

tff(c_6682,plain,
    ( '#skF_6' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_8])).

tff(c_6689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_4710,c_6682])).

tff(c_6690,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6426])).

tff(c_6697,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_6100])).

tff(c_4770,plain,(
    ! [A_306,B_307] : k3_zfmisc_1(A_306,B_307,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_4])).

tff(c_6711,plain,(
    ! [A_306,B_307] : k3_zfmisc_1(A_306,B_307,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6690,c_6690,c_4770])).

tff(c_6867,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6711,c_6099])).

tff(c_6869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6697,c_6867])).

tff(c_6871,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5080])).

tff(c_4857,plain,(
    ! [D_318,A_315,B_316,C_317] :
      ( k1_xboole_0 = D_318
      | k3_zfmisc_1(A_315,B_316,C_317) = k1_xboole_0
      | k4_zfmisc_1(A_315,B_316,C_317,D_318) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_2])).

tff(c_6895,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6871,c_4857])).

tff(c_6900,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_6895])).

tff(c_6943,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6900,c_4766])).

tff(c_6953,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_6943])).

tff(c_6971,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6953,c_2])).

tff(c_6981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_6971])).

tff(c_6983,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4704])).

tff(c_6984,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_4705,c_26])).

tff(c_6989,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6983,c_6984])).

tff(c_7124,plain,(
    ! [A_457,B_458,C_459,D_460] : k2_zfmisc_1(k3_zfmisc_1(A_457,B_458,C_459),D_460) = k4_zfmisc_1(A_457,B_458,C_459,D_460) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7393,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( k2_relat_1(k4_zfmisc_1(A_490,B_491,C_492,D_493)) = D_493
      | k1_xboole_0 = D_493
      | k3_zfmisc_1(A_490,B_491,C_492) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_8])).

tff(c_7414,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6989,c_7393])).

tff(c_7421,plain,
    ( k2_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_7414])).

tff(c_7490,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7421])).

tff(c_7014,plain,(
    ! [A_446,B_447,C_448] : k2_zfmisc_1(k2_zfmisc_1(A_446,B_447),C_448) = k3_zfmisc_1(A_446,B_447,C_448) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7026,plain,(
    ! [C_448,A_446,B_447] :
      ( k1_xboole_0 = C_448
      | k2_zfmisc_1(A_446,B_447) = k1_xboole_0
      | k3_zfmisc_1(A_446,B_447,C_448) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7014,c_2])).

tff(c_7510,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7490,c_7026])).

tff(c_7513,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7510])).

tff(c_7530,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7513,c_2])).

tff(c_7540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_7530])).

tff(c_7541,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7510])).

tff(c_7338,plain,(
    ! [D_483,A_484,B_485,C_486] :
      ( k1_xboole_0 = D_483
      | k3_zfmisc_1(A_484,B_485,C_486) = k1_xboole_0
      | k4_zfmisc_1(A_484,B_485,C_486,D_483) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_2])).

tff(c_7353,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6989,c_7338])).

tff(c_7362,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_7353])).

tff(c_7363,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7362])).

tff(c_7546,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7541,c_7363])).

tff(c_7506,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_7490,c_14])).

tff(c_7511,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7506])).

tff(c_7773,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7541,c_7511])).

tff(c_7774,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7773,c_6989])).

tff(c_7776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7546,c_7774])).

tff(c_7778,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7421])).

tff(c_7856,plain,(
    ! [A_520,B_521,C_522,D_523] :
      ( k1_relat_1(k4_zfmisc_1(A_520,B_521,C_522,D_523)) = k3_zfmisc_1(A_520,B_521,C_522)
      | k1_xboole_0 = D_523
      | k3_zfmisc_1(A_520,B_521,C_522) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_10])).

tff(c_7880,plain,
    ( k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6989,c_7856])).

tff(c_7888,plain,(
    k1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_7778,c_18,c_7880])).

tff(c_7136,plain,(
    ! [A_457,B_458,C_459,D_460] :
      ( k1_relat_1(k4_zfmisc_1(A_457,B_458,C_459,D_460)) = k3_zfmisc_1(A_457,B_458,C_459)
      | k1_xboole_0 = D_460
      | k3_zfmisc_1(A_457,B_458,C_459) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_10])).

tff(c_7892,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7888,c_7136])).

tff(c_7898,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3')
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_7892])).

tff(c_7901,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7898])).

tff(c_7914,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7901,c_7026])).

tff(c_7925,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_7914])).

tff(c_7946,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7925,c_2])).

tff(c_7957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_7946])).

tff(c_7958,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_7898])).

tff(c_7076,plain,(
    ! [A_453,B_454] :
      ( k2_relat_1(k2_zfmisc_1(A_453,B_454)) = B_454
      | k1_xboole_0 = B_454
      | k1_xboole_0 = A_453 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7085,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7076])).

tff(c_7971,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7958,c_7085])).

tff(c_8076,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7971])).

tff(c_8095,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8076,c_2])).

tff(c_8106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_8095])).

tff(c_8108,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7971])).

tff(c_6982,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4704])).

tff(c_8107,plain,
    ( k1_xboole_0 = '#skF_7'
    | k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7971])).

tff(c_8111,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_8107])).

tff(c_8115,plain,
    ( '#skF_7' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8111,c_7085])).

tff(c_8122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8108,c_20,c_6982,c_8115])).

tff(c_8123,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8107])).

tff(c_7959,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7898])).

tff(c_8128,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8123,c_7959])).

tff(c_7030,plain,(
    ! [A_446,B_447] : k3_zfmisc_1(A_446,B_447,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7014,c_4])).

tff(c_8143,plain,(
    ! [A_446,B_447] : k3_zfmisc_1(A_446,B_447,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8123,c_8123,c_7030])).

tff(c_8293,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8143,c_7958])).

tff(c_8295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8128,c_8293])).

tff(c_8297,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7362])).

tff(c_7139,plain,(
    ! [D_460,A_457,B_458,C_459] :
      ( k1_xboole_0 = D_460
      | k3_zfmisc_1(A_457,B_458,C_459) = k1_xboole_0
      | k4_zfmisc_1(A_457,B_458,C_459,D_460) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_2])).

tff(c_8346,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8297,c_7139])).

tff(c_8351,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_8346])).

tff(c_8362,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8351,c_7026])).

tff(c_8372,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_8362])).

tff(c_8390,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8372,c_2])).

tff(c_8400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_8390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.13  
% 5.54/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.13  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.54/2.13  
% 5.54/2.13  %Foreground sorts:
% 5.54/2.13  
% 5.54/2.13  
% 5.54/2.13  %Background operators:
% 5.54/2.13  
% 5.54/2.13  
% 5.54/2.13  %Foreground operators:
% 5.54/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.54/2.13  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 5.54/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.54/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.54/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.54/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.54/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.54/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.54/2.13  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.54/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.54/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.54/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.54/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.54/2.13  
% 5.66/2.17  tff(f_66, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 5.66/2.17  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 5.66/2.17  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 5.66/2.17  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.66/2.17  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.66/2.17  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_16, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_60, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 5.66/2.17  tff(c_26, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.17  tff(c_191, plain, (![A_29, B_30, C_31, D_32]: (k2_zfmisc_1(k3_zfmisc_1(A_29, B_30, C_31), D_32)=k4_zfmisc_1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.17  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.66/2.17  tff(c_527, plain, (![A_67, B_68, C_69, D_70]: (k2_relat_1(k4_zfmisc_1(A_67, B_68, C_69, D_70))=D_70 | k1_xboole_0=D_70 | k3_zfmisc_1(A_67, B_68, C_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 5.66/2.17  tff(c_548, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_527])).
% 5.66/2.17  tff(c_651, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_548])).
% 5.66/2.17  tff(c_85, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.17  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.17  tff(c_97, plain, (![C_20, A_18, B_19]: (k1_xboole_0=C_20 | k2_zfmisc_1(A_18, B_19)=k1_xboole_0 | k3_zfmisc_1(A_18, B_19, C_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 5.66/2.17  tff(c_672, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_651, c_97])).
% 5.66/2.17  tff(c_676, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_672])).
% 5.66/2.17  tff(c_701, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_676, c_2])).
% 5.66/2.17  tff(c_703, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_701])).
% 5.66/2.17  tff(c_405, plain, (![D_55, A_56, B_57, C_58]: (k1_xboole_0=D_55 | k3_zfmisc_1(A_56, B_57, C_58)=k1_xboole_0 | k4_zfmisc_1(A_56, B_57, C_58, D_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 5.66/2.17  tff(c_420, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_405])).
% 5.66/2.17  tff(c_429, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_420])).
% 5.66/2.17  tff(c_784, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_703, c_429])).
% 5.66/2.17  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.17  tff(c_14, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.17  tff(c_668, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_651, c_14])).
% 5.66/2.17  tff(c_673, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_668])).
% 5.66/2.17  tff(c_983, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_703, c_673])).
% 5.66/2.17  tff(c_984, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_983, c_26])).
% 5.66/2.17  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_784, c_984])).
% 5.66/2.17  tff(c_987, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_701])).
% 5.66/2.17  tff(c_1070, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_987, c_429])).
% 5.66/2.17  tff(c_1298, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_987, c_673])).
% 5.66/2.17  tff(c_1299, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_26])).
% 5.66/2.17  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1070, c_1299])).
% 5.66/2.17  tff(c_1302, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_672])).
% 5.66/2.17  tff(c_1308, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1302, c_429])).
% 5.66/2.17  tff(c_1540, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1302, c_673])).
% 5.66/2.17  tff(c_1541, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_26])).
% 5.66/2.17  tff(c_1543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1308, c_1541])).
% 5.66/2.17  tff(c_1545, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_548])).
% 5.66/2.17  tff(c_10, plain, (![A_3, B_4]: (k1_relat_1(k2_zfmisc_1(A_3, B_4))=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.66/2.17  tff(c_556, plain, (![A_71, B_72, C_73, D_74]: (k1_relat_1(k4_zfmisc_1(A_71, B_72, C_73, D_74))=k3_zfmisc_1(A_71, B_72, C_73) | k1_xboole_0=D_74 | k3_zfmisc_1(A_71, B_72, C_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_10])).
% 5.66/2.17  tff(c_577, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_556])).
% 5.66/2.17  tff(c_1546, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1545, c_577])).
% 5.66/2.17  tff(c_1547, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1546])).
% 5.66/2.17  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.17  tff(c_210, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_4])).
% 5.66/2.17  tff(c_1559, plain, (![A_29, B_30, C_31]: (k4_zfmisc_1(A_29, B_30, C_31, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1547, c_210])).
% 5.66/2.17  tff(c_1803, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_26])).
% 5.66/2.17  tff(c_1552, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_429])).
% 5.66/2.17  tff(c_1850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1803, c_1552])).
% 5.66/2.17  tff(c_1852, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_1546])).
% 5.66/2.17  tff(c_1544, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_548])).
% 5.66/2.17  tff(c_1853, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_1852, c_1544])).
% 5.66/2.17  tff(c_197, plain, (![A_29, B_30, C_31, D_32]: (k2_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=D_32 | k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 5.66/2.17  tff(c_1857, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1853, c_197])).
% 5.66/2.17  tff(c_1863, plain, ('#skF_8'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_1857])).
% 5.66/2.17  tff(c_1866, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1863])).
% 5.66/2.17  tff(c_1879, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1866, c_97])).
% 5.66/2.17  tff(c_1890, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_1879])).
% 5.66/2.17  tff(c_1925, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1890, c_2])).
% 5.66/2.17  tff(c_1936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_1925])).
% 5.66/2.17  tff(c_1938, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1863])).
% 5.66/2.17  tff(c_1851, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1546])).
% 5.66/2.17  tff(c_203, plain, (![A_29, B_30, C_31, D_32]: (k1_relat_1(k4_zfmisc_1(A_29, B_30, C_31, D_32))=k3_zfmisc_1(A_29, B_30, C_31) | k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_10])).
% 5.66/2.17  tff(c_1965, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1851, c_203])).
% 5.66/2.17  tff(c_1971, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1938, c_18, c_1965])).
% 5.66/2.17  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.17  tff(c_148, plain, (![A_25, B_26]: (k2_relat_1(k2_zfmisc_1(A_25, B_26))=B_26 | k1_xboole_0=B_26 | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.66/2.17  tff(c_157, plain, (![A_5, B_6, C_7]: (k2_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_148])).
% 5.66/2.17  tff(c_1985, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1971, c_157])).
% 5.66/2.17  tff(c_2142, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1985])).
% 5.66/2.17  tff(c_2167, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2142, c_2])).
% 5.66/2.17  tff(c_2169, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2167])).
% 5.66/2.17  tff(c_2171, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_1938])).
% 5.66/2.17  tff(c_117, plain, (![B_2, C_20]: (k3_zfmisc_1(k1_xboole_0, B_2, C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 5.66/2.17  tff(c_121, plain, (![B_2, C_20]: (k3_zfmisc_1(k1_xboole_0, B_2, C_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_117])).
% 5.66/2.17  tff(c_2183, plain, (![B_2, C_20]: (k3_zfmisc_1('#skF_5', B_2, C_20)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_2169, c_121])).
% 5.66/2.17  tff(c_2293, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_1971])).
% 5.66/2.17  tff(c_2295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2171, c_2293])).
% 5.66/2.17  tff(c_2296, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2167])).
% 5.66/2.17  tff(c_2301, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2296, c_1938])).
% 5.66/2.17  tff(c_2155, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_2142, c_12])).
% 5.66/2.17  tff(c_2166, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2155])).
% 5.66/2.17  tff(c_2389, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2296, c_2166])).
% 5.66/2.17  tff(c_2390, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2389, c_1971])).
% 5.66/2.17  tff(c_2451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2301, c_2390])).
% 5.66/2.17  tff(c_2452, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_1985])).
% 5.66/2.17  tff(c_2454, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_2452])).
% 5.66/2.17  tff(c_2458, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2454, c_157])).
% 5.66/2.17  tff(c_2464, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_2458])).
% 5.66/2.17  tff(c_2467, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2464])).
% 5.66/2.17  tff(c_2486, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2467, c_2])).
% 5.66/2.17  tff(c_2497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_2486])).
% 5.66/2.17  tff(c_2499, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2464])).
% 5.66/2.17  tff(c_2453, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1985])).
% 5.66/2.17  tff(c_2498, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_2464])).
% 5.66/2.17  tff(c_2503, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_1971])).
% 5.66/2.17  tff(c_94, plain, (![A_18, B_19, C_20]: (k1_relat_1(k3_zfmisc_1(A_18, B_19, C_20))=k2_zfmisc_1(A_18, B_19) | k1_xboole_0=C_20 | k2_zfmisc_1(A_18, B_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_10])).
% 5.66/2.17  tff(c_2516, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2503, c_94])).
% 5.66/2.17  tff(c_2532, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2453, c_20, c_2516])).
% 5.66/2.17  tff(c_2563, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2532, c_94])).
% 5.66/2.17  tff(c_2569, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2499, c_20, c_2563])).
% 5.66/2.17  tff(c_2583, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2569, c_8])).
% 5.66/2.17  tff(c_2661, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2583])).
% 5.66/2.17  tff(c_2663, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_2499])).
% 5.66/2.17  tff(c_2683, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_2661, c_6])).
% 5.66/2.17  tff(c_2725, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2683, c_2569])).
% 5.66/2.17  tff(c_2727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2663, c_2725])).
% 5.66/2.17  tff(c_2729, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2583])).
% 5.66/2.17  tff(c_2589, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2569, c_10])).
% 5.66/2.17  tff(c_2730, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2729, c_2589])).
% 5.66/2.17  tff(c_2731, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2730])).
% 5.66/2.17  tff(c_2734, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_2499])).
% 5.66/2.17  tff(c_2753, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_2731, c_4])).
% 5.66/2.17  tff(c_2783, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_2569])).
% 5.66/2.17  tff(c_2785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2734, c_2783])).
% 5.66/2.17  tff(c_2786, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_5'), inference(splitRight, [status(thm)], [c_2730])).
% 5.66/2.17  tff(c_2791, plain, ('#skF_5'='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2786, c_10])).
% 5.66/2.17  tff(c_2798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_60, c_2791])).
% 5.66/2.17  tff(c_2799, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2452])).
% 5.66/2.17  tff(c_2802, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2799, c_1938])).
% 5.66/2.17  tff(c_101, plain, (![A_18, B_19]: (k3_zfmisc_1(A_18, B_19, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 5.66/2.17  tff(c_2817, plain, (![A_18, B_19]: (k3_zfmisc_1(A_18, B_19, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2799, c_2799, c_101])).
% 5.66/2.17  tff(c_2951, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2817, c_1971])).
% 5.66/2.17  tff(c_2953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2802, c_2951])).
% 5.66/2.17  tff(c_2955, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_420])).
% 5.66/2.17  tff(c_206, plain, (![D_32, A_29, B_30, C_31]: (k1_xboole_0=D_32 | k3_zfmisc_1(A_29, B_30, C_31)=k1_xboole_0 | k4_zfmisc_1(A_29, B_30, C_31, D_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_2])).
% 5.66/2.17  tff(c_2960, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2955, c_206])).
% 5.66/2.17  tff(c_2965, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_2960])).
% 5.66/2.17  tff(c_2973, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2965, c_97])).
% 5.66/2.17  tff(c_2982, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_2973])).
% 5.66/2.17  tff(c_3000, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2982, c_2])).
% 5.66/2.17  tff(c_3010, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_3000])).
% 5.66/2.17  tff(c_3011, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 5.66/2.17  tff(c_3017, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3011])).
% 5.66/2.17  tff(c_3012, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 5.66/2.17  tff(c_3120, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_26])).
% 5.66/2.17  tff(c_3149, plain, (![A_182, B_183, C_184, D_185]: (k2_zfmisc_1(k3_zfmisc_1(A_182, B_183, C_184), D_185)=k4_zfmisc_1(A_182, B_183, C_184, D_185))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.17  tff(c_3391, plain, (![A_212, B_213, C_214, D_215]: (k2_relat_1(k4_zfmisc_1(A_212, B_213, C_214, D_215))=D_215 | k1_xboole_0=D_215 | k3_zfmisc_1(A_212, B_213, C_214)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3149, c_8])).
% 5.66/2.17  tff(c_3412, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3120, c_3391])).
% 5.66/2.17  tff(c_3513, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3412])).
% 5.66/2.17  tff(c_3038, plain, (![A_171, B_172, C_173]: (k2_zfmisc_1(k2_zfmisc_1(A_171, B_172), C_173)=k3_zfmisc_1(A_171, B_172, C_173))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.17  tff(c_3050, plain, (![C_173, A_171, B_172]: (k1_xboole_0=C_173 | k2_zfmisc_1(A_171, B_172)=k1_xboole_0 | k3_zfmisc_1(A_171, B_172, C_173)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3038, c_2])).
% 5.66/2.17  tff(c_3533, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3513, c_3050])).
% 5.66/2.17  tff(c_3536, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3533])).
% 5.66/2.17  tff(c_3552, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3536, c_2])).
% 5.66/2.17  tff(c_3561, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24, c_3552])).
% 5.66/2.17  tff(c_3529, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_3513, c_14])).
% 5.66/2.17  tff(c_3534, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3529])).
% 5.66/2.17  tff(c_3808, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3561, c_3534])).
% 5.66/2.17  tff(c_3809, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3808, c_3120])).
% 5.66/2.17  tff(c_3363, plain, (![D_208, A_209, B_210, C_211]: (k1_xboole_0=D_208 | k3_zfmisc_1(A_209, B_210, C_211)=k1_xboole_0 | k4_zfmisc_1(A_209, B_210, C_211, D_208)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3149, c_2])).
% 5.66/2.17  tff(c_3378, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3120, c_3363])).
% 5.66/2.17  tff(c_3387, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3378])).
% 5.66/2.17  tff(c_3566, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3561, c_3387])).
% 5.66/2.17  tff(c_4040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3809, c_3566])).
% 5.66/2.17  tff(c_4041, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3533])).
% 5.66/2.17  tff(c_4045, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_3387])).
% 5.66/2.17  tff(c_4282, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_3534])).
% 5.66/2.17  tff(c_4283, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4282, c_3120])).
% 5.66/2.17  tff(c_4285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4045, c_4283])).
% 5.66/2.17  tff(c_4286, plain, (k1_xboole_0='#skF_8' | k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitRight, [status(thm)], [c_3412])).
% 5.66/2.17  tff(c_4318, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_8'), inference(splitLeft, [status(thm)], [c_4286])).
% 5.66/2.17  tff(c_3161, plain, (![A_182, B_183, C_184, D_185]: (k2_relat_1(k4_zfmisc_1(A_182, B_183, C_184, D_185))=D_185 | k1_xboole_0=D_185 | k3_zfmisc_1(A_182, B_183, C_184)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3149, c_8])).
% 5.66/2.17  tff(c_4322, plain, ('#skF_8'='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4318, c_3161])).
% 5.66/2.17  tff(c_4328, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_3017, c_4322])).
% 5.66/2.17  tff(c_4343, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4328, c_3050])).
% 5.66/2.17  tff(c_4354, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_4343])).
% 5.66/2.17  tff(c_4372, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4354, c_2])).
% 5.66/2.17  tff(c_4382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_4372])).
% 5.66/2.17  tff(c_4383, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_4286])).
% 5.66/2.17  tff(c_4388, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_3387])).
% 5.66/2.17  tff(c_3168, plain, (![A_182, B_183, C_184]: (k4_zfmisc_1(A_182, B_183, C_184, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3149, c_4])).
% 5.66/2.17  tff(c_4396, plain, (![A_182, B_183, C_184]: (k4_zfmisc_1(A_182, B_183, C_184, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_4383, c_3168])).
% 5.66/2.17  tff(c_4576, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_3120])).
% 5.66/2.17  tff(c_4646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4388, c_4576])).
% 5.66/2.17  tff(c_4648, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3378])).
% 5.66/2.17  tff(c_3164, plain, (![D_185, A_182, B_183, C_184]: (k1_xboole_0=D_185 | k3_zfmisc_1(A_182, B_183, C_184)=k1_xboole_0 | k4_zfmisc_1(A_182, B_183, C_184, D_185)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3149, c_2])).
% 5.66/2.17  tff(c_4653, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4648, c_3164])).
% 5.66/2.17  tff(c_4658, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_4653])).
% 5.66/2.17  tff(c_4666, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4658, c_3050])).
% 5.66/2.17  tff(c_4675, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_4666])).
% 5.66/2.17  tff(c_4693, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4675, c_2])).
% 5.66/2.17  tff(c_4703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_4693])).
% 5.66/2.17  tff(c_4704, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_3011])).
% 5.66/2.17  tff(c_4710, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_4704])).
% 5.66/2.17  tff(c_4705, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_3011])).
% 5.66/2.17  tff(c_4791, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_3012, c_26])).
% 5.66/2.17  tff(c_4842, plain, (![A_315, B_316, C_317, D_318]: (k2_zfmisc_1(k3_zfmisc_1(A_315, B_316, C_317), D_318)=k4_zfmisc_1(A_315, B_316, C_317, D_318))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.17  tff(c_5149, plain, (![A_350, B_351, C_352, D_353]: (k2_relat_1(k4_zfmisc_1(A_350, B_351, C_352, D_353))=D_353 | k1_xboole_0=D_353 | k3_zfmisc_1(A_350, B_351, C_352)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4842, c_8])).
% 5.66/2.17  tff(c_5170, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4791, c_5149])).
% 5.66/2.17  tff(c_5177, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_5170])).
% 5.66/2.17  tff(c_5178, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5177])).
% 5.66/2.17  tff(c_4751, plain, (![A_306, B_307, C_308]: (k2_zfmisc_1(k2_zfmisc_1(A_306, B_307), C_308)=k3_zfmisc_1(A_306, B_307, C_308))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.17  tff(c_4766, plain, (![C_308, A_306, B_307]: (k1_xboole_0=C_308 | k2_zfmisc_1(A_306, B_307)=k1_xboole_0 | k3_zfmisc_1(A_306, B_307, C_308)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4751, c_2])).
% 5.66/2.17  tff(c_5195, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5178, c_4766])).
% 5.66/2.17  tff(c_5198, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5195])).
% 5.66/2.17  tff(c_5214, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5198, c_2])).
% 5.66/2.17  tff(c_5223, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24, c_5214])).
% 5.66/2.17  tff(c_5191, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_5178, c_14])).
% 5.66/2.17  tff(c_5196, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5191])).
% 5.66/2.17  tff(c_5496, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_5196])).
% 5.66/2.17  tff(c_5497, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5496, c_4791])).
% 5.66/2.17  tff(c_5056, plain, (![D_341, A_342, B_343, C_344]: (k1_xboole_0=D_341 | k3_zfmisc_1(A_342, B_343, C_344)=k1_xboole_0 | k4_zfmisc_1(A_342, B_343, C_344, D_341)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4842, c_2])).
% 5.66/2.17  tff(c_5071, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4791, c_5056])).
% 5.66/2.17  tff(c_5080, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_5071])).
% 5.66/2.17  tff(c_5145, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5080])).
% 5.66/2.17  tff(c_5228, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5223, c_5145])).
% 5.66/2.17  tff(c_5705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5497, c_5228])).
% 5.66/2.17  tff(c_5706, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5195])).
% 5.66/2.17  tff(c_5710, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5706, c_5145])).
% 5.66/2.17  tff(c_5954, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5706, c_5196])).
% 5.66/2.17  tff(c_5955, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5954, c_4791])).
% 5.66/2.17  tff(c_5957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5710, c_5955])).
% 5.66/2.17  tff(c_5959, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5177])).
% 5.66/2.17  tff(c_6005, plain, (![A_408, B_409, C_410, D_411]: (k1_relat_1(k4_zfmisc_1(A_408, B_409, C_410, D_411))=k3_zfmisc_1(A_408, B_409, C_410) | k1_xboole_0=D_411 | k3_zfmisc_1(A_408, B_409, C_410)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4842, c_10])).
% 5.66/2.17  tff(c_6026, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4791, c_6005])).
% 5.66/2.17  tff(c_6033, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_5959, c_18, c_6026])).
% 5.66/2.17  tff(c_4851, plain, (![A_315, B_316, C_317, D_318]: (k1_relat_1(k4_zfmisc_1(A_315, B_316, C_317, D_318))=k3_zfmisc_1(A_315, B_316, C_317) | k1_xboole_0=D_318 | k3_zfmisc_1(A_315, B_316, C_317)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4842, c_10])).
% 5.66/2.17  tff(c_6037, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6033, c_4851])).
% 5.66/2.17  tff(c_6043, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_6037])).
% 5.66/2.17  tff(c_6046, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6043])).
% 5.66/2.17  tff(c_6059, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6046, c_4766])).
% 5.66/2.17  tff(c_6070, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_6059])).
% 5.66/2.17  tff(c_6088, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6070, c_2])).
% 5.66/2.17  tff(c_6098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_6088])).
% 5.66/2.17  tff(c_6099, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_6043])).
% 5.66/2.17  tff(c_4763, plain, (![A_306, B_307, C_308]: (k2_relat_1(k3_zfmisc_1(A_306, B_307, C_308))=C_308 | k1_xboole_0=C_308 | k2_zfmisc_1(A_306, B_307)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4751, c_8])).
% 5.66/2.17  tff(c_6112, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6099, c_4763])).
% 5.66/2.17  tff(c_6283, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6112])).
% 5.66/2.17  tff(c_6302, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6283, c_2])).
% 5.66/2.17  tff(c_6312, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24, c_6302])).
% 5.66/2.17  tff(c_6100, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_6043])).
% 5.66/2.17  tff(c_6317, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6312, c_6100])).
% 5.66/2.17  tff(c_6293, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_6283, c_12])).
% 5.66/2.17  tff(c_6307, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6293])).
% 5.66/2.17  tff(c_6422, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6312, c_6307])).
% 5.66/2.17  tff(c_6423, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6422, c_6099])).
% 5.66/2.17  tff(c_6425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6317, c_6423])).
% 5.66/2.17  tff(c_6426, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_6112])).
% 5.66/2.17  tff(c_6428, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_6426])).
% 5.66/2.17  tff(c_6432, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6428, c_4763])).
% 5.66/2.17  tff(c_6438, plain, ('#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_6432])).
% 5.66/2.17  tff(c_6442, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6438])).
% 5.66/2.17  tff(c_6461, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6442, c_2])).
% 5.66/2.17  tff(c_6472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_6461])).
% 5.66/2.17  tff(c_6474, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_6438])).
% 5.66/2.17  tff(c_6427, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_6112])).
% 5.66/2.17  tff(c_6473, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_6438])).
% 5.66/2.17  tff(c_6477, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6473, c_6099])).
% 5.66/2.17  tff(c_4760, plain, (![A_306, B_307, C_308]: (k1_relat_1(k3_zfmisc_1(A_306, B_307, C_308))=k2_zfmisc_1(A_306, B_307) | k1_xboole_0=C_308 | k2_zfmisc_1(A_306, B_307)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4751, c_10])).
% 5.66/2.17  tff(c_6500, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6477, c_4760])).
% 5.66/2.17  tff(c_6515, plain, (k1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_6427, c_20, c_6500])).
% 5.66/2.17  tff(c_6525, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6515, c_4760])).
% 5.66/2.17  tff(c_6531, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_6474, c_20, c_6525])).
% 5.66/2.17  tff(c_6551, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6531, c_8])).
% 5.66/2.17  tff(c_6561, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24, c_6551])).
% 5.66/2.17  tff(c_6565, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6561])).
% 5.66/2.17  tff(c_6566, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_6474])).
% 5.66/2.17  tff(c_6587, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_6565, c_4])).
% 5.66/2.17  tff(c_6597, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6587, c_6531])).
% 5.66/2.17  tff(c_6676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6566, c_6597])).
% 5.66/2.17  tff(c_6677, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))='#skF_6'), inference(splitRight, [status(thm)], [c_6561])).
% 5.66/2.17  tff(c_6682, plain, ('#skF_6'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6677, c_8])).
% 5.66/2.17  tff(c_6689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_4710, c_6682])).
% 5.66/2.17  tff(c_6690, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6426])).
% 5.66/2.17  tff(c_6697, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_6100])).
% 5.66/2.17  tff(c_4770, plain, (![A_306, B_307]: (k3_zfmisc_1(A_306, B_307, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4751, c_4])).
% 5.66/2.17  tff(c_6711, plain, (![A_306, B_307]: (k3_zfmisc_1(A_306, B_307, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6690, c_6690, c_4770])).
% 5.66/2.17  tff(c_6867, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6711, c_6099])).
% 5.66/2.17  tff(c_6869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6697, c_6867])).
% 5.66/2.17  tff(c_6871, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5080])).
% 5.66/2.17  tff(c_4857, plain, (![D_318, A_315, B_316, C_317]: (k1_xboole_0=D_318 | k3_zfmisc_1(A_315, B_316, C_317)=k1_xboole_0 | k4_zfmisc_1(A_315, B_316, C_317, D_318)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4842, c_2])).
% 5.66/2.17  tff(c_6895, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6871, c_4857])).
% 5.66/2.17  tff(c_6900, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_6895])).
% 5.66/2.17  tff(c_6943, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6900, c_4766])).
% 5.66/2.17  tff(c_6953, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_6943])).
% 5.66/2.17  tff(c_6971, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6953, c_2])).
% 5.66/2.17  tff(c_6981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_6971])).
% 5.66/2.17  tff(c_6983, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_4704])).
% 5.66/2.17  tff(c_6984, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_4705, c_26])).
% 5.66/2.17  tff(c_6989, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6983, c_6984])).
% 5.66/2.17  tff(c_7124, plain, (![A_457, B_458, C_459, D_460]: (k2_zfmisc_1(k3_zfmisc_1(A_457, B_458, C_459), D_460)=k4_zfmisc_1(A_457, B_458, C_459, D_460))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.17  tff(c_7393, plain, (![A_490, B_491, C_492, D_493]: (k2_relat_1(k4_zfmisc_1(A_490, B_491, C_492, D_493))=D_493 | k1_xboole_0=D_493 | k3_zfmisc_1(A_490, B_491, C_492)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7124, c_8])).
% 5.66/2.17  tff(c_7414, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6989, c_7393])).
% 5.66/2.17  tff(c_7421, plain, (k2_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_7414])).
% 5.66/2.17  tff(c_7490, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7421])).
% 5.66/2.17  tff(c_7014, plain, (![A_446, B_447, C_448]: (k2_zfmisc_1(k2_zfmisc_1(A_446, B_447), C_448)=k3_zfmisc_1(A_446, B_447, C_448))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.17  tff(c_7026, plain, (![C_448, A_446, B_447]: (k1_xboole_0=C_448 | k2_zfmisc_1(A_446, B_447)=k1_xboole_0 | k3_zfmisc_1(A_446, B_447, C_448)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7014, c_2])).
% 5.66/2.17  tff(c_7510, plain, (k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7490, c_7026])).
% 5.66/2.17  tff(c_7513, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7510])).
% 5.66/2.17  tff(c_7530, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7513, c_2])).
% 5.66/2.17  tff(c_7540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_7530])).
% 5.66/2.17  tff(c_7541, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7510])).
% 5.66/2.17  tff(c_7338, plain, (![D_483, A_484, B_485, C_486]: (k1_xboole_0=D_483 | k3_zfmisc_1(A_484, B_485, C_486)=k1_xboole_0 | k4_zfmisc_1(A_484, B_485, C_486, D_483)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7124, c_2])).
% 5.66/2.17  tff(c_7353, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6989, c_7338])).
% 5.66/2.17  tff(c_7362, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_7353])).
% 5.66/2.17  tff(c_7363, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7362])).
% 5.66/2.17  tff(c_7546, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7541, c_7363])).
% 5.66/2.17  tff(c_7506, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_7490, c_14])).
% 5.66/2.17  tff(c_7511, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_7506])).
% 5.66/2.17  tff(c_7773, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7541, c_7511])).
% 5.66/2.17  tff(c_7774, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7773, c_6989])).
% 5.66/2.17  tff(c_7776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7546, c_7774])).
% 5.66/2.17  tff(c_7778, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7421])).
% 5.66/2.17  tff(c_7856, plain, (![A_520, B_521, C_522, D_523]: (k1_relat_1(k4_zfmisc_1(A_520, B_521, C_522, D_523))=k3_zfmisc_1(A_520, B_521, C_522) | k1_xboole_0=D_523 | k3_zfmisc_1(A_520, B_521, C_522)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7124, c_10])).
% 5.66/2.17  tff(c_7880, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6989, c_7856])).
% 5.66/2.17  tff(c_7888, plain, (k1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_7778, c_18, c_7880])).
% 5.66/2.17  tff(c_7136, plain, (![A_457, B_458, C_459, D_460]: (k1_relat_1(k4_zfmisc_1(A_457, B_458, C_459, D_460))=k3_zfmisc_1(A_457, B_458, C_459) | k1_xboole_0=D_460 | k3_zfmisc_1(A_457, B_458, C_459)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7124, c_10])).
% 5.66/2.17  tff(c_7892, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7888, c_7136])).
% 5.66/2.17  tff(c_7898, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3') | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_7892])).
% 5.66/2.17  tff(c_7901, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7898])).
% 5.66/2.17  tff(c_7914, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7901, c_7026])).
% 5.66/2.17  tff(c_7925, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_7914])).
% 5.66/2.17  tff(c_7946, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7925, c_2])).
% 5.66/2.17  tff(c_7957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_7946])).
% 5.66/2.17  tff(c_7958, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_7898])).
% 5.66/2.17  tff(c_7076, plain, (![A_453, B_454]: (k2_relat_1(k2_zfmisc_1(A_453, B_454))=B_454 | k1_xboole_0=B_454 | k1_xboole_0=A_453)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.66/2.17  tff(c_7085, plain, (![A_5, B_6, C_7]: (k2_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_7076])).
% 5.66/2.17  tff(c_7971, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7958, c_7085])).
% 5.66/2.17  tff(c_8076, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7971])).
% 5.66/2.17  tff(c_8095, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8076, c_2])).
% 5.66/2.17  tff(c_8106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_8095])).
% 5.66/2.17  tff(c_8108, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7971])).
% 5.66/2.17  tff(c_6982, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_4704])).
% 5.66/2.17  tff(c_8107, plain, (k1_xboole_0='#skF_7' | k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitRight, [status(thm)], [c_7971])).
% 5.66/2.17  tff(c_8111, plain, (k2_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))='#skF_7'), inference(splitLeft, [status(thm)], [c_8107])).
% 5.66/2.17  tff(c_8115, plain, ('#skF_7'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8111, c_7085])).
% 5.66/2.17  tff(c_8122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8108, c_20, c_6982, c_8115])).
% 5.66/2.17  tff(c_8123, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8107])).
% 5.66/2.17  tff(c_7959, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7898])).
% 5.66/2.17  tff(c_8128, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8123, c_7959])).
% 5.66/2.17  tff(c_7030, plain, (![A_446, B_447]: (k3_zfmisc_1(A_446, B_447, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7014, c_4])).
% 5.66/2.17  tff(c_8143, plain, (![A_446, B_447]: (k3_zfmisc_1(A_446, B_447, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8123, c_8123, c_7030])).
% 5.66/2.17  tff(c_8293, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8143, c_7958])).
% 5.66/2.17  tff(c_8295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8128, c_8293])).
% 5.66/2.17  tff(c_8297, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7362])).
% 5.66/2.17  tff(c_7139, plain, (![D_460, A_457, B_458, C_459]: (k1_xboole_0=D_460 | k3_zfmisc_1(A_457, B_458, C_459)=k1_xboole_0 | k4_zfmisc_1(A_457, B_458, C_459, D_460)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7124, c_2])).
% 5.66/2.17  tff(c_8346, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8297, c_7139])).
% 5.66/2.17  tff(c_8351, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_8346])).
% 5.66/2.17  tff(c_8362, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8351, c_7026])).
% 5.66/2.17  tff(c_8372, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_8362])).
% 5.66/2.17  tff(c_8390, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8372, c_2])).
% 5.66/2.17  tff(c_8400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_8390])).
% 5.66/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.17  
% 5.66/2.17  Inference rules
% 5.66/2.17  ----------------------
% 5.66/2.17  #Ref     : 0
% 5.66/2.17  #Sup     : 1977
% 5.66/2.17  #Fact    : 0
% 5.66/2.17  #Define  : 0
% 5.66/2.17  #Split   : 37
% 5.66/2.17  #Chain   : 0
% 5.66/2.17  #Close   : 0
% 5.66/2.17  
% 5.66/2.17  Ordering : KBO
% 5.66/2.17  
% 5.66/2.17  Simplification rules
% 5.66/2.17  ----------------------
% 5.66/2.17  #Subsume      : 62
% 5.66/2.17  #Demod        : 1848
% 5.66/2.17  #Tautology    : 1280
% 5.66/2.17  #SimpNegUnit  : 184
% 5.66/2.17  #BackRed      : 518
% 5.66/2.17  
% 5.66/2.17  #Partial instantiations: 0
% 5.66/2.17  #Strategies tried      : 1
% 5.66/2.17  
% 5.66/2.17  Timing (in seconds)
% 5.66/2.17  ----------------------
% 5.66/2.17  Preprocessing        : 0.29
% 5.66/2.17  Parsing              : 0.15
% 5.66/2.17  CNF conversion       : 0.02
% 5.66/2.17  Main loop            : 1.06
% 5.66/2.17  Inferencing          : 0.40
% 5.66/2.17  Reduction            : 0.36
% 5.66/2.17  Demodulation         : 0.25
% 5.66/2.17  BG Simplification    : 0.05
% 5.66/2.17  Subsumption          : 0.16
% 5.66/2.17  Abstraction          : 0.07
% 5.66/2.17  MUC search           : 0.00
% 5.66/2.17  Cooper               : 0.00
% 5.66/2.17  Total                : 1.44
% 5.66/2.17  Index Insertion      : 0.00
% 5.66/2.17  Index Deletion       : 0.00
% 5.66/2.17  Index Matching       : 0.00
% 5.66/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
