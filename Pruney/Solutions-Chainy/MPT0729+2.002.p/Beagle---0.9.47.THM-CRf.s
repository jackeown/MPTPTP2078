%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 32.54s
% Output     : CNFRefutation 32.71s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 250 expanded)
%              Number of leaves         :   37 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 ( 360 expanded)
%              Number of equality atoms :   46 ( 141 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_96,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_94,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_56,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_72,plain,(
    ! [A_47] : r2_hidden(A_47,k1_ordinal1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1407,plain,(
    ! [A_170,B_171,C_172] :
      ( r1_tarski(k2_tarski(A_170,B_171),C_172)
      | ~ r2_hidden(B_171,C_172)
      | ~ r2_hidden(A_170,C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5504,plain,(
    ! [A_342,C_343] :
      ( r1_tarski(k1_tarski(A_342),C_343)
      | ~ r2_hidden(A_342,C_343)
      | ~ r2_hidden(A_342,C_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1407])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16277,plain,(
    ! [A_613,C_614] :
      ( k4_xboole_0(k1_tarski(A_613),C_614) = k1_xboole_0
      | ~ r2_hidden(A_613,C_614) ) ),
    inference(resolution,[status(thm)],[c_5504,c_30])).

tff(c_34,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16481,plain,(
    ! [C_614,A_613] :
      ( k2_xboole_0(C_614,k1_tarski(A_613)) = k2_xboole_0(C_614,k1_xboole_0)
      | ~ r2_hidden(A_613,C_614) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16277,c_34])).

tff(c_33352,plain,(
    ! [C_845,A_846] :
      ( k2_xboole_0(C_845,k1_tarski(A_846)) = C_845
      | ~ r2_hidden(A_846,C_845) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16481])).

tff(c_42,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_271,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1448,plain,(
    ! [B_175,A_176] : k3_tarski(k2_tarski(B_175,A_176)) = k2_xboole_0(A_176,B_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_52,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1454,plain,(
    ! [B_175,A_176] : k2_xboole_0(B_175,A_176) = k2_xboole_0(A_176,B_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_1448,c_52])).

tff(c_33817,plain,(
    ! [A_846,C_845] :
      ( k2_xboole_0(k1_tarski(A_846),C_845) = C_845
      | ~ r2_hidden(A_846,C_845) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33352,c_1454])).

tff(c_40,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_186,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_202,plain,(
    ! [B_10] : k4_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_186])).

tff(c_871,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_tarski(k4_xboole_0(A_147,B_148),C_149)
      | ~ r1_tarski(A_147,k2_xboole_0(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_891,plain,(
    ! [C_149,B_10] :
      ( r1_tarski(k1_xboole_0,C_149)
      | ~ r1_tarski(B_10,k2_xboole_0(B_10,C_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_871])).

tff(c_895,plain,(
    ! [C_149] : r1_tarski(k1_xboole_0,C_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_891])).

tff(c_201,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_186])).

tff(c_2035,plain,(
    ! [D_187,A_188,B_189] :
      ( r2_hidden(D_187,k4_xboole_0(A_188,B_189))
      | r2_hidden(D_187,B_189)
      | ~ r2_hidden(D_187,A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6914,plain,(
    ! [A_387,B_388,D_389] :
      ( ~ r1_tarski(k4_xboole_0(A_387,B_388),D_389)
      | r2_hidden(D_389,B_388)
      | ~ r2_hidden(D_389,A_387) ) ),
    inference(resolution,[status(thm)],[c_2035,c_74])).

tff(c_6988,plain,(
    ! [D_389,A_22,B_23] :
      ( ~ r1_tarski(k1_xboole_0,D_389)
      | r2_hidden(D_389,k2_xboole_0(A_22,B_23))
      | ~ r2_hidden(D_389,A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_6914])).

tff(c_7050,plain,(
    ! [D_389,A_22,B_23] :
      ( r2_hidden(D_389,k2_xboole_0(A_22,B_23))
      | ~ r2_hidden(D_389,A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_6988])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_357,plain,(
    ! [B_87,C_88,A_89] :
      ( r2_hidden(B_87,C_88)
      | ~ r1_tarski(k2_tarski(A_89,B_87),C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_392,plain,(
    ! [B_90,A_91] : r2_hidden(B_90,k2_tarski(A_91,B_90)) ),
    inference(resolution,[status(thm)],[c_26,c_357])).

tff(c_409,plain,(
    ! [A_92] : r2_hidden(A_92,k1_tarski(A_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_392])).

tff(c_418,plain,(
    ! [A_94] : ~ r1_tarski(k1_tarski(A_94),A_94) ),
    inference(resolution,[status(thm)],[c_409,c_74])).

tff(c_423,plain,(
    ! [B_12] : k4_xboole_0(k1_tarski(B_12),B_12) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_418])).

tff(c_16679,plain,(
    ! [C_615] : ~ r2_hidden(C_615,C_615) ),
    inference(superposition,[status(thm),theory(equality)],[c_16277,c_423])).

tff(c_16710,plain,(
    ! [A_22,B_23] : ~ r2_hidden(k2_xboole_0(A_22,B_23),A_22) ),
    inference(resolution,[status(thm)],[c_7050,c_16679])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    k1_ordinal1('#skF_3') = k1_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_tarski(A_46)) = k1_ordinal1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1065,plain,(
    ! [A_159,B_160,C_161] : k4_xboole_0(k4_xboole_0(A_159,B_160),C_161) = k4_xboole_0(A_159,k2_xboole_0(B_160,C_161)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9539,plain,(
    ! [C_455,A_456,B_457] : k2_xboole_0(C_455,k4_xboole_0(A_456,k2_xboole_0(B_457,C_455))) = k2_xboole_0(C_455,k4_xboole_0(A_456,B_457)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_34])).

tff(c_9781,plain,(
    ! [C_455,B_457] : k2_xboole_0(C_455,k4_xboole_0(k2_xboole_0(B_457,C_455),B_457)) = k2_xboole_0(C_455,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_9539])).

tff(c_19566,plain,(
    ! [C_683,B_684] : k2_xboole_0(C_683,k4_xboole_0(k2_xboole_0(B_684,C_683),B_684)) = C_683 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9781])).

tff(c_22266,plain,(
    ! [B_718,A_719] : k2_xboole_0(B_718,k4_xboole_0(k2_xboole_0(B_718,A_719),A_719)) = B_718 ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_19566])).

tff(c_40918,plain,(
    ! [A_913] : k2_xboole_0(A_913,k4_xboole_0(k1_ordinal1(A_913),k1_tarski(A_913))) = A_913 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_22266])).

tff(c_41411,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0(k1_ordinal1('#skF_4'),k1_tarski('#skF_3'))) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_40918])).

tff(c_10786,plain,(
    ! [D_475,A_476,B_477] :
      ( r2_hidden(D_475,k2_xboole_0(A_476,B_477))
      | ~ r2_hidden(D_475,A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_6988])).

tff(c_29582,plain,(
    ! [D_818,B_819,A_820] :
      ( r2_hidden(D_818,k2_xboole_0(B_819,A_820))
      | ~ r2_hidden(D_818,A_820) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_10786])).

tff(c_536,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(A_110,C_111)
      | ~ r1_tarski(k2_tarski(A_110,B_112),C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1014,plain,(
    ! [A_155,C_156] :
      ( r2_hidden(A_155,C_156)
      | ~ r1_tarski(k1_tarski(A_155),C_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_536])).

tff(c_1037,plain,(
    ! [A_157,B_158] : r2_hidden(A_157,k2_xboole_0(k1_tarski(A_157),B_158)) ),
    inference(resolution,[status(thm)],[c_40,c_1014])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1059,plain,(
    ! [A_157,B_158] : ~ r2_hidden(k2_xboole_0(k1_tarski(A_157),B_158),A_157) ),
    inference(resolution,[status(thm)],[c_1037,c_2])).

tff(c_30037,plain,(
    ! [B_819,A_820,B_158] : ~ r2_hidden(k2_xboole_0(k1_tarski(k2_xboole_0(B_819,A_820)),B_158),A_820) ),
    inference(resolution,[status(thm)],[c_29582,c_1059])).

tff(c_53620,plain,(
    ! [B_1062] : ~ r2_hidden(k2_xboole_0(k1_tarski('#skF_3'),B_1062),k4_xboole_0(k1_ordinal1('#skF_4'),k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41411,c_30037])).

tff(c_53673,plain,(
    ! [B_1062] :
      ( r2_hidden(k2_xboole_0(k1_tarski('#skF_3'),B_1062),k1_tarski('#skF_3'))
      | ~ r2_hidden(k2_xboole_0(k1_tarski('#skF_3'),B_1062),k1_ordinal1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_53620])).

tff(c_53710,plain,(
    ! [B_1063] : ~ r2_hidden(k2_xboole_0(k1_tarski('#skF_3'),B_1063),k1_ordinal1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_16710,c_53673])).

tff(c_54175,plain,(
    ! [C_1070] :
      ( ~ r2_hidden(C_1070,k1_ordinal1('#skF_4'))
      | ~ r2_hidden('#skF_3',C_1070) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33817,c_53710])).

tff(c_54267,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_54175])).

tff(c_76,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k4_xboole_0(A_16,B_17),C_18) = k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1701,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden(A_180,k4_xboole_0(B_181,k1_tarski(C_182)))
      | C_182 = A_180
      | ~ r2_hidden(A_180,B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14422,plain,(
    ! [A_563,A_564,B_565,C_566] :
      ( r2_hidden(A_563,k4_xboole_0(A_564,k2_xboole_0(B_565,k1_tarski(C_566))))
      | C_566 = A_563
      | ~ r2_hidden(A_563,k4_xboole_0(A_564,B_565)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1701])).

tff(c_93399,plain,(
    ! [A_1417,A_1418,A_1419] :
      ( r2_hidden(A_1417,k4_xboole_0(A_1418,k1_ordinal1(A_1419)))
      | A_1419 = A_1417
      | ~ r2_hidden(A_1417,k4_xboole_0(A_1418,A_1419)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14422])).

tff(c_62,plain,(
    ! [C_43,B_42] : ~ r2_hidden(C_43,k4_xboole_0(B_42,k1_tarski(C_43))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3529,plain,(
    ! [C_258,A_259,B_260] : ~ r2_hidden(C_258,k4_xboole_0(A_259,k2_xboole_0(B_260,k1_tarski(C_258)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_62])).

tff(c_3587,plain,(
    ! [A_261,A_262] : ~ r2_hidden(A_261,k4_xboole_0(A_262,k1_ordinal1(A_261))) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3529])).

tff(c_3622,plain,(
    ! [A_262] : ~ r2_hidden('#skF_3',k4_xboole_0(A_262,k1_ordinal1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3587])).

tff(c_93999,plain,(
    ! [A_1418] :
      ( '#skF_3' = '#skF_4'
      | ~ r2_hidden('#skF_3',k4_xboole_0(A_1418,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_93399,c_3622])).

tff(c_94440,plain,(
    ! [A_1420] : ~ r2_hidden('#skF_3',k4_xboole_0(A_1420,'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_93999])).

tff(c_94476,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_3','#skF_4')
      | ~ r2_hidden('#skF_3',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_94440])).

tff(c_94490,plain,(
    ! [A_3] : ~ r2_hidden('#skF_3',A_3) ),
    inference(negUnitSimplification,[status(thm)],[c_54267,c_94476])).

tff(c_3625,plain,(
    ! [A_263] : ~ r2_hidden('#skF_3',k4_xboole_0(A_263,k1_ordinal1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_3587])).

tff(c_3652,plain,(
    ! [A_264,B_265] : ~ r2_hidden('#skF_3',k4_xboole_0(A_264,k2_xboole_0(B_265,k1_ordinal1('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3625])).

tff(c_3707,plain,(
    ! [B_265,A_3] :
      ( r2_hidden('#skF_3',k2_xboole_0(B_265,k1_ordinal1('#skF_4')))
      | ~ r2_hidden('#skF_3',A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_3652])).

tff(c_4801,plain,(
    ! [A_3] : ~ r2_hidden('#skF_3',A_3) ),
    inference(splitLeft,[status(thm)],[c_3707])).

tff(c_85,plain,(
    ! [A_51] : r2_hidden(A_51,k1_ordinal1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_85])).

tff(c_4803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4801,c_88])).

tff(c_4805,plain,(
    ! [B_313] : r2_hidden('#skF_3',k2_xboole_0(B_313,k1_ordinal1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_3707])).

tff(c_4828,plain,(
    ! [B_175] : r2_hidden('#skF_3',k2_xboole_0(k1_ordinal1('#skF_4'),B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_4805])).

tff(c_94495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94490,c_4828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:38:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.54/23.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.54/23.50  
% 32.54/23.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.54/23.50  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 32.54/23.50  
% 32.54/23.50  %Foreground sorts:
% 32.54/23.50  
% 32.54/23.50  
% 32.54/23.50  %Background operators:
% 32.54/23.50  
% 32.54/23.50  
% 32.54/23.50  %Foreground operators:
% 32.54/23.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 32.54/23.50  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 32.54/23.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.54/23.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.54/23.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 32.54/23.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.54/23.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.54/23.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 32.54/23.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.54/23.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 32.54/23.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.54/23.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 32.54/23.50  tff('#skF_3', type, '#skF_3': $i).
% 32.54/23.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 32.54/23.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.54/23.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 32.54/23.50  tff('#skF_4', type, '#skF_4': $i).
% 32.54/23.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.54/23.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.54/23.50  
% 32.71/23.53  tff(f_96, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 32.71/23.53  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 32.71/23.53  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 32.71/23.53  tff(f_80, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 32.71/23.53  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 32.71/23.53  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 32.71/23.53  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 32.71/23.53  tff(f_74, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 32.71/23.53  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 32.71/23.53  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.71/23.53  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 32.71/23.53  tff(f_40, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 32.71/23.53  tff(f_101, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 32.71/23.53  tff(f_106, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 32.71/23.53  tff(f_94, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 32.71/23.53  tff(f_56, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 32.71/23.53  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 32.71/23.53  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 32.71/23.53  tff(c_72, plain, (![A_47]: (r2_hidden(A_47, k1_ordinal1(A_47)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 32.71/23.53  tff(c_32, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_52])).
% 32.71/23.53  tff(c_44, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 32.71/23.53  tff(c_1407, plain, (![A_170, B_171, C_172]: (r1_tarski(k2_tarski(A_170, B_171), C_172) | ~r2_hidden(B_171, C_172) | ~r2_hidden(A_170, C_172))), inference(cnfTransformation, [status(thm)], [f_80])).
% 32.71/23.53  tff(c_5504, plain, (![A_342, C_343]: (r1_tarski(k1_tarski(A_342), C_343) | ~r2_hidden(A_342, C_343) | ~r2_hidden(A_342, C_343))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1407])).
% 32.71/23.53  tff(c_30, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 32.71/23.53  tff(c_16277, plain, (![A_613, C_614]: (k4_xboole_0(k1_tarski(A_613), C_614)=k1_xboole_0 | ~r2_hidden(A_613, C_614))), inference(resolution, [status(thm)], [c_5504, c_30])).
% 32.71/23.53  tff(c_34, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 32.71/23.53  tff(c_16481, plain, (![C_614, A_613]: (k2_xboole_0(C_614, k1_tarski(A_613))=k2_xboole_0(C_614, k1_xboole_0) | ~r2_hidden(A_613, C_614))), inference(superposition, [status(thm), theory('equality')], [c_16277, c_34])).
% 32.71/23.53  tff(c_33352, plain, (![C_845, A_846]: (k2_xboole_0(C_845, k1_tarski(A_846))=C_845 | ~r2_hidden(A_846, C_845))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16481])).
% 32.71/23.53  tff(c_42, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 32.71/23.53  tff(c_271, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.71/23.53  tff(c_1448, plain, (![B_175, A_176]: (k3_tarski(k2_tarski(B_175, A_176))=k2_xboole_0(A_176, B_175))), inference(superposition, [status(thm), theory('equality')], [c_42, c_271])).
% 32.71/23.53  tff(c_52, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_74])).
% 32.71/23.53  tff(c_1454, plain, (![B_175, A_176]: (k2_xboole_0(B_175, A_176)=k2_xboole_0(A_176, B_175))), inference(superposition, [status(thm), theory('equality')], [c_1448, c_52])).
% 32.71/23.53  tff(c_33817, plain, (![A_846, C_845]: (k2_xboole_0(k1_tarski(A_846), C_845)=C_845 | ~r2_hidden(A_846, C_845))), inference(superposition, [status(thm), theory('equality')], [c_33352, c_1454])).
% 32.71/23.53  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 32.71/23.53  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 32.71/23.53  tff(c_186, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_50])).
% 32.71/23.53  tff(c_202, plain, (![B_10]: (k4_xboole_0(B_10, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_186])).
% 32.71/23.53  tff(c_871, plain, (![A_147, B_148, C_149]: (r1_tarski(k4_xboole_0(A_147, B_148), C_149) | ~r1_tarski(A_147, k2_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 32.71/23.53  tff(c_891, plain, (![C_149, B_10]: (r1_tarski(k1_xboole_0, C_149) | ~r1_tarski(B_10, k2_xboole_0(B_10, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_871])).
% 32.71/23.53  tff(c_895, plain, (![C_149]: (r1_tarski(k1_xboole_0, C_149))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_891])).
% 32.71/23.53  tff(c_201, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_186])).
% 32.71/23.53  tff(c_2035, plain, (![D_187, A_188, B_189]: (r2_hidden(D_187, k4_xboole_0(A_188, B_189)) | r2_hidden(D_187, B_189) | ~r2_hidden(D_187, A_188))), inference(cnfTransformation, [status(thm)], [f_40])).
% 32.71/23.53  tff(c_74, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_101])).
% 32.71/23.53  tff(c_6914, plain, (![A_387, B_388, D_389]: (~r1_tarski(k4_xboole_0(A_387, B_388), D_389) | r2_hidden(D_389, B_388) | ~r2_hidden(D_389, A_387))), inference(resolution, [status(thm)], [c_2035, c_74])).
% 32.71/23.53  tff(c_6988, plain, (![D_389, A_22, B_23]: (~r1_tarski(k1_xboole_0, D_389) | r2_hidden(D_389, k2_xboole_0(A_22, B_23)) | ~r2_hidden(D_389, A_22))), inference(superposition, [status(thm), theory('equality')], [c_201, c_6914])).
% 32.71/23.53  tff(c_7050, plain, (![D_389, A_22, B_23]: (r2_hidden(D_389, k2_xboole_0(A_22, B_23)) | ~r2_hidden(D_389, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_6988])).
% 32.71/23.53  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 32.71/23.53  tff(c_357, plain, (![B_87, C_88, A_89]: (r2_hidden(B_87, C_88) | ~r1_tarski(k2_tarski(A_89, B_87), C_88))), inference(cnfTransformation, [status(thm)], [f_80])).
% 32.71/23.53  tff(c_392, plain, (![B_90, A_91]: (r2_hidden(B_90, k2_tarski(A_91, B_90)))), inference(resolution, [status(thm)], [c_26, c_357])).
% 32.71/23.53  tff(c_409, plain, (![A_92]: (r2_hidden(A_92, k1_tarski(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_392])).
% 32.71/23.53  tff(c_418, plain, (![A_94]: (~r1_tarski(k1_tarski(A_94), A_94))), inference(resolution, [status(thm)], [c_409, c_74])).
% 32.71/23.53  tff(c_423, plain, (![B_12]: (k4_xboole_0(k1_tarski(B_12), B_12)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_418])).
% 32.71/23.53  tff(c_16679, plain, (![C_615]: (~r2_hidden(C_615, C_615))), inference(superposition, [status(thm), theory('equality')], [c_16277, c_423])).
% 32.71/23.53  tff(c_16710, plain, (![A_22, B_23]: (~r2_hidden(k2_xboole_0(A_22, B_23), A_22))), inference(resolution, [status(thm)], [c_7050, c_16679])).
% 32.71/23.53  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 32.71/23.53  tff(c_78, plain, (k1_ordinal1('#skF_3')=k1_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 32.71/23.53  tff(c_70, plain, (![A_46]: (k2_xboole_0(A_46, k1_tarski(A_46))=k1_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_94])).
% 32.71/23.53  tff(c_1065, plain, (![A_159, B_160, C_161]: (k4_xboole_0(k4_xboole_0(A_159, B_160), C_161)=k4_xboole_0(A_159, k2_xboole_0(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 32.71/23.53  tff(c_9539, plain, (![C_455, A_456, B_457]: (k2_xboole_0(C_455, k4_xboole_0(A_456, k2_xboole_0(B_457, C_455)))=k2_xboole_0(C_455, k4_xboole_0(A_456, B_457)))), inference(superposition, [status(thm), theory('equality')], [c_1065, c_34])).
% 32.71/23.53  tff(c_9781, plain, (![C_455, B_457]: (k2_xboole_0(C_455, k4_xboole_0(k2_xboole_0(B_457, C_455), B_457))=k2_xboole_0(C_455, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_202, c_9539])).
% 32.71/23.53  tff(c_19566, plain, (![C_683, B_684]: (k2_xboole_0(C_683, k4_xboole_0(k2_xboole_0(B_684, C_683), B_684))=C_683)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9781])).
% 32.71/23.53  tff(c_22266, plain, (![B_718, A_719]: (k2_xboole_0(B_718, k4_xboole_0(k2_xboole_0(B_718, A_719), A_719))=B_718)), inference(superposition, [status(thm), theory('equality')], [c_1454, c_19566])).
% 32.71/23.53  tff(c_40918, plain, (![A_913]: (k2_xboole_0(A_913, k4_xboole_0(k1_ordinal1(A_913), k1_tarski(A_913)))=A_913)), inference(superposition, [status(thm), theory('equality')], [c_70, c_22266])).
% 32.71/23.53  tff(c_41411, plain, (k2_xboole_0('#skF_3', k4_xboole_0(k1_ordinal1('#skF_4'), k1_tarski('#skF_3')))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_78, c_40918])).
% 32.71/23.53  tff(c_10786, plain, (![D_475, A_476, B_477]: (r2_hidden(D_475, k2_xboole_0(A_476, B_477)) | ~r2_hidden(D_475, A_476))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_6988])).
% 32.71/23.53  tff(c_29582, plain, (![D_818, B_819, A_820]: (r2_hidden(D_818, k2_xboole_0(B_819, A_820)) | ~r2_hidden(D_818, A_820))), inference(superposition, [status(thm), theory('equality')], [c_1454, c_10786])).
% 32.71/23.53  tff(c_536, plain, (![A_110, C_111, B_112]: (r2_hidden(A_110, C_111) | ~r1_tarski(k2_tarski(A_110, B_112), C_111))), inference(cnfTransformation, [status(thm)], [f_80])).
% 32.71/23.53  tff(c_1014, plain, (![A_155, C_156]: (r2_hidden(A_155, C_156) | ~r1_tarski(k1_tarski(A_155), C_156))), inference(superposition, [status(thm), theory('equality')], [c_44, c_536])).
% 32.71/23.53  tff(c_1037, plain, (![A_157, B_158]: (r2_hidden(A_157, k2_xboole_0(k1_tarski(A_157), B_158)))), inference(resolution, [status(thm)], [c_40, c_1014])).
% 32.71/23.53  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 32.71/23.53  tff(c_1059, plain, (![A_157, B_158]: (~r2_hidden(k2_xboole_0(k1_tarski(A_157), B_158), A_157))), inference(resolution, [status(thm)], [c_1037, c_2])).
% 32.71/23.53  tff(c_30037, plain, (![B_819, A_820, B_158]: (~r2_hidden(k2_xboole_0(k1_tarski(k2_xboole_0(B_819, A_820)), B_158), A_820))), inference(resolution, [status(thm)], [c_29582, c_1059])).
% 32.71/23.53  tff(c_53620, plain, (![B_1062]: (~r2_hidden(k2_xboole_0(k1_tarski('#skF_3'), B_1062), k4_xboole_0(k1_ordinal1('#skF_4'), k1_tarski('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_41411, c_30037])).
% 32.71/23.53  tff(c_53673, plain, (![B_1062]: (r2_hidden(k2_xboole_0(k1_tarski('#skF_3'), B_1062), k1_tarski('#skF_3')) | ~r2_hidden(k2_xboole_0(k1_tarski('#skF_3'), B_1062), k1_ordinal1('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_53620])).
% 32.71/23.53  tff(c_53710, plain, (![B_1063]: (~r2_hidden(k2_xboole_0(k1_tarski('#skF_3'), B_1063), k1_ordinal1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_16710, c_53673])).
% 32.71/23.53  tff(c_54175, plain, (![C_1070]: (~r2_hidden(C_1070, k1_ordinal1('#skF_4')) | ~r2_hidden('#skF_3', C_1070))), inference(superposition, [status(thm), theory('equality')], [c_33817, c_53710])).
% 32.71/23.53  tff(c_54267, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_54175])).
% 32.71/23.53  tff(c_76, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_106])).
% 32.71/23.53  tff(c_36, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k4_xboole_0(A_16, B_17), C_18)=k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 32.71/23.53  tff(c_1701, plain, (![A_180, B_181, C_182]: (r2_hidden(A_180, k4_xboole_0(B_181, k1_tarski(C_182))) | C_182=A_180 | ~r2_hidden(A_180, B_181))), inference(cnfTransformation, [status(thm)], [f_87])).
% 32.71/23.53  tff(c_14422, plain, (![A_563, A_564, B_565, C_566]: (r2_hidden(A_563, k4_xboole_0(A_564, k2_xboole_0(B_565, k1_tarski(C_566)))) | C_566=A_563 | ~r2_hidden(A_563, k4_xboole_0(A_564, B_565)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1701])).
% 32.71/23.53  tff(c_93399, plain, (![A_1417, A_1418, A_1419]: (r2_hidden(A_1417, k4_xboole_0(A_1418, k1_ordinal1(A_1419))) | A_1419=A_1417 | ~r2_hidden(A_1417, k4_xboole_0(A_1418, A_1419)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_14422])).
% 32.71/23.53  tff(c_62, plain, (![C_43, B_42]: (~r2_hidden(C_43, k4_xboole_0(B_42, k1_tarski(C_43))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 32.71/23.53  tff(c_3529, plain, (![C_258, A_259, B_260]: (~r2_hidden(C_258, k4_xboole_0(A_259, k2_xboole_0(B_260, k1_tarski(C_258)))))), inference(superposition, [status(thm), theory('equality')], [c_1065, c_62])).
% 32.71/23.53  tff(c_3587, plain, (![A_261, A_262]: (~r2_hidden(A_261, k4_xboole_0(A_262, k1_ordinal1(A_261))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_3529])).
% 32.71/23.53  tff(c_3622, plain, (![A_262]: (~r2_hidden('#skF_3', k4_xboole_0(A_262, k1_ordinal1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_3587])).
% 32.71/23.53  tff(c_93999, plain, (![A_1418]: ('#skF_3'='#skF_4' | ~r2_hidden('#skF_3', k4_xboole_0(A_1418, '#skF_4')))), inference(resolution, [status(thm)], [c_93399, c_3622])).
% 32.71/23.53  tff(c_94440, plain, (![A_1420]: (~r2_hidden('#skF_3', k4_xboole_0(A_1420, '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_93999])).
% 32.71/23.53  tff(c_94476, plain, (![A_3]: (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', A_3))), inference(resolution, [status(thm)], [c_4, c_94440])).
% 32.71/23.53  tff(c_94490, plain, (![A_3]: (~r2_hidden('#skF_3', A_3))), inference(negUnitSimplification, [status(thm)], [c_54267, c_94476])).
% 32.71/23.53  tff(c_3625, plain, (![A_263]: (~r2_hidden('#skF_3', k4_xboole_0(A_263, k1_ordinal1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_78, c_3587])).
% 32.71/23.53  tff(c_3652, plain, (![A_264, B_265]: (~r2_hidden('#skF_3', k4_xboole_0(A_264, k2_xboole_0(B_265, k1_ordinal1('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_3625])).
% 32.71/23.53  tff(c_3707, plain, (![B_265, A_3]: (r2_hidden('#skF_3', k2_xboole_0(B_265, k1_ordinal1('#skF_4'))) | ~r2_hidden('#skF_3', A_3))), inference(resolution, [status(thm)], [c_4, c_3652])).
% 32.71/23.53  tff(c_4801, plain, (![A_3]: (~r2_hidden('#skF_3', A_3))), inference(splitLeft, [status(thm)], [c_3707])).
% 32.71/23.53  tff(c_85, plain, (![A_51]: (r2_hidden(A_51, k1_ordinal1(A_51)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 32.71/23.53  tff(c_88, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_85])).
% 32.71/23.53  tff(c_4803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4801, c_88])).
% 32.71/23.53  tff(c_4805, plain, (![B_313]: (r2_hidden('#skF_3', k2_xboole_0(B_313, k1_ordinal1('#skF_4'))))), inference(splitRight, [status(thm)], [c_3707])).
% 32.71/23.53  tff(c_4828, plain, (![B_175]: (r2_hidden('#skF_3', k2_xboole_0(k1_ordinal1('#skF_4'), B_175)))), inference(superposition, [status(thm), theory('equality')], [c_1454, c_4805])).
% 32.71/23.53  tff(c_94495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94490, c_4828])).
% 32.71/23.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.71/23.53  
% 32.71/23.53  Inference rules
% 32.71/23.53  ----------------------
% 32.71/23.53  #Ref     : 0
% 32.71/23.53  #Sup     : 23559
% 32.71/23.53  #Fact    : 0
% 32.71/23.53  #Define  : 0
% 32.71/23.53  #Split   : 8
% 32.71/23.53  #Chain   : 0
% 32.71/23.53  #Close   : 0
% 32.71/23.53  
% 32.71/23.53  Ordering : KBO
% 32.71/23.53  
% 32.71/23.53  Simplification rules
% 32.71/23.53  ----------------------
% 32.71/23.53  #Subsume      : 10046
% 32.71/23.53  #Demod        : 15360
% 32.71/23.53  #Tautology    : 5312
% 32.71/23.53  #SimpNegUnit  : 956
% 32.71/23.53  #BackRed      : 23
% 32.71/23.53  
% 32.71/23.53  #Partial instantiations: 0
% 32.71/23.53  #Strategies tried      : 1
% 32.71/23.53  
% 32.71/23.53  Timing (in seconds)
% 32.71/23.53  ----------------------
% 32.71/23.53  Preprocessing        : 0.36
% 32.71/23.53  Parsing              : 0.19
% 32.71/23.53  CNF conversion       : 0.03
% 32.71/23.53  Main loop            : 22.33
% 32.71/23.53  Inferencing          : 2.12
% 32.71/23.53  Reduction            : 12.03
% 32.71/23.53  Demodulation         : 8.93
% 32.71/23.53  BG Simplification    : 0.22
% 32.71/23.53  Subsumption          : 7.09
% 32.71/23.53  Abstraction          : 0.35
% 32.71/23.53  MUC search           : 0.00
% 32.71/23.53  Cooper               : 0.00
% 32.71/23.53  Total                : 22.74
% 32.71/23.53  Index Insertion      : 0.00
% 32.71/23.53  Index Deletion       : 0.00
% 32.71/23.53  Index Matching       : 0.00
% 32.71/23.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
