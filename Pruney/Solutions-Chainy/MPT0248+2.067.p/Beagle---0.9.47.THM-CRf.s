%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:13 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 255 expanded)
%              Number of leaves         :   42 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 438 expanded)
%              Number of equality atoms :   79 ( 338 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_74,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_76,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_80,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_141,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_28])).

tff(c_501,plain,(
    ! [B_126,A_127] :
      ( k1_tarski(B_126) = A_127
      | k1_xboole_0 = A_127
      | ~ r1_tarski(A_127,k1_tarski(B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_516,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_141,c_501])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_130,c_516])).

tff(c_534,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_70,plain,(
    ! [B_66] : r1_tarski(k1_xboole_0,k1_tarski(B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_536,plain,(
    ! [B_66] : r1_tarski('#skF_6',k1_tarski(B_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_70])).

tff(c_637,plain,(
    ! [A_142,B_143] :
      ( k2_xboole_0(A_142,B_143) = B_143
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_655,plain,(
    ! [B_66] : k2_xboole_0('#skF_6',k1_tarski(B_66)) = k1_tarski(B_66) ),
    inference(resolution,[status(thm)],[c_536,c_637])).

tff(c_533,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k1_tarski(A_63),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_770,plain,(
    ! [B_164,A_165] :
      ( B_164 = A_165
      | ~ r1_tarski(B_164,A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_792,plain,(
    ! [B_166] :
      ( k1_tarski(B_166) = '#skF_6'
      | ~ r1_tarski(k1_tarski(B_166),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_536,c_770])).

tff(c_802,plain,(
    ! [A_167] :
      ( k1_tarski(A_167) = '#skF_6'
      | ~ r2_hidden(A_167,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_792])).

tff(c_812,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_802])).

tff(c_813,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_743,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158,B_159),A_158)
      | r1_tarski(A_158,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_759,plain,(
    ! [A_160,B_161] :
      ( ~ v1_xboole_0(A_160)
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_743,c_4])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_768,plain,(
    ! [A_160,B_161] :
      ( k2_xboole_0(A_160,B_161) = B_161
      | ~ v1_xboole_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_759,c_24])).

tff(c_825,plain,(
    ! [B_161] : k2_xboole_0('#skF_6',B_161) = B_161 ),
    inference(resolution,[status(thm)],[c_813,c_768])).

tff(c_827,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_80])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_827])).

tff(c_830,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_711,plain,(
    ! [A_150,B_151] :
      ( r2_hidden(A_150,B_151)
      | ~ r1_tarski(k1_tarski(A_150),B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_724,plain,(
    ! [A_150,B_23] : r2_hidden(A_150,k2_xboole_0(k1_tarski(A_150),B_23)) ),
    inference(resolution,[status(thm)],[c_28,c_711])).

tff(c_940,plain,(
    ! [B_179] : r2_hidden('#skF_1'('#skF_6'),k2_xboole_0('#skF_6',B_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_724])).

tff(c_957,plain,(
    ! [B_180] : r2_hidden('#skF_1'('#skF_6'),k1_tarski(B_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_940])).

tff(c_36,plain,(
    ! [C_34,A_30] :
      ( C_34 = A_30
      | ~ r2_hidden(C_34,k1_tarski(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1080,plain,(
    '#skF_1'('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_957,c_36])).

tff(c_1081,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_830])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1081])).

tff(c_1252,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1253,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1380,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_1253,c_78])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3067,plain,(
    ! [A_2657,B_2658] : k5_xboole_0(k5_xboole_0(A_2657,B_2658),k2_xboole_0(A_2657,B_2658)) = k3_xboole_0(A_2657,B_2658) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3149,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,A_27)) = k3_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3067])).

tff(c_3159,plain,(
    ! [A_27] : k5_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_3149])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2641,plain,(
    ! [A_2644,B_2645,C_2646] : k5_xboole_0(k5_xboole_0(A_2644,B_2645),C_2646) = k5_xboole_0(A_2644,k5_xboole_0(B_2645,C_2646)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2884,plain,(
    ! [A_2653,C_2654] : k5_xboole_0(A_2653,k5_xboole_0(A_2653,C_2654)) = k5_xboole_0(k1_xboole_0,C_2654) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2641])).

tff(c_2956,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = k5_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2884])).

tff(c_3392,plain,(
    ! [A_2663,B_2664] : k5_xboole_0(A_2663,k5_xboole_0(B_2664,A_2663)) = B_2664 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3159,c_2956])).

tff(c_3161,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3159,c_2956])).

tff(c_3395,plain,(
    ! [B_2664,A_2663] : k5_xboole_0(k5_xboole_0(B_2664,A_2663),B_2664) = A_2663 ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_3161])).

tff(c_1268,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_80])).

tff(c_3146,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_3067])).

tff(c_4368,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3395,c_3146])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2080,plain,(
    ! [B_2614,A_2615] :
      ( k1_tarski(B_2614) = A_2615
      | k1_xboole_0 = A_2615
      | ~ r1_tarski(A_2615,k1_tarski(B_2614)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2099,plain,(
    ! [A_2615] :
      ( k1_tarski('#skF_5') = A_2615
      | k1_xboole_0 = A_2615
      | ~ r1_tarski(A_2615,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_2080])).

tff(c_2119,plain,(
    ! [A_2616] :
      ( A_2616 = '#skF_6'
      | k1_xboole_0 = A_2616
      | ~ r1_tarski(A_2616,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_2099])).

tff(c_2154,plain,(
    ! [B_21] :
      ( k3_xboole_0('#skF_6',B_21) = '#skF_6'
      | k3_xboole_0('#skF_6',B_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_2119])).

tff(c_4476,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_4368,c_2154])).

tff(c_4490,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4368,c_4476])).

tff(c_4492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1252,c_1380,c_4490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/2.01  
% 4.88/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/2.01  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.88/2.01  
% 4.88/2.01  %Foreground sorts:
% 4.88/2.01  
% 4.88/2.01  
% 4.88/2.01  %Background operators:
% 4.88/2.01  
% 4.88/2.01  
% 4.88/2.01  %Foreground operators:
% 4.88/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/2.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.88/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/2.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.88/2.01  tff('#skF_7', type, '#skF_7': $i).
% 4.88/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.88/2.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.88/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.88/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/2.01  tff('#skF_5', type, '#skF_5': $i).
% 4.88/2.01  tff('#skF_6', type, '#skF_6': $i).
% 4.88/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/2.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.88/2.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.88/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/2.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.88/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/2.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.88/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.88/2.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.88/2.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.88/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.88/2.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.88/2.01  
% 4.88/2.03  tff(f_116, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.88/2.03  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.88/2.03  tff(f_95, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.88/2.03  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.88/2.03  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.88/2.03  tff(f_89, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.88/2.03  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/2.03  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.88/2.03  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.88/2.03  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.88/2.03  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.88/2.03  tff(f_62, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.88/2.03  tff(f_64, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.88/2.03  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.88/2.03  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.88/2.03  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.88/2.03  tff(c_74, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.88/2.03  tff(c_130, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 4.88/2.03  tff(c_76, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.88/2.03  tff(c_132, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_76])).
% 4.88/2.03  tff(c_80, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.88/2.03  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.88/2.03  tff(c_141, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_28])).
% 4.88/2.03  tff(c_501, plain, (![B_126, A_127]: (k1_tarski(B_126)=A_127 | k1_xboole_0=A_127 | ~r1_tarski(A_127, k1_tarski(B_126)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.88/2.03  tff(c_516, plain, (k1_tarski('#skF_5')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_141, c_501])).
% 4.88/2.03  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_130, c_516])).
% 4.88/2.03  tff(c_534, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 4.88/2.03  tff(c_70, plain, (![B_66]: (r1_tarski(k1_xboole_0, k1_tarski(B_66)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.88/2.03  tff(c_536, plain, (![B_66]: (r1_tarski('#skF_6', k1_tarski(B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_70])).
% 4.88/2.03  tff(c_637, plain, (![A_142, B_143]: (k2_xboole_0(A_142, B_143)=B_143 | ~r1_tarski(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.88/2.03  tff(c_655, plain, (![B_66]: (k2_xboole_0('#skF_6', k1_tarski(B_66))=k1_tarski(B_66))), inference(resolution, [status(thm)], [c_536, c_637])).
% 4.88/2.03  tff(c_533, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 4.88/2.03  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/2.03  tff(c_64, plain, (![A_63, B_64]: (r1_tarski(k1_tarski(A_63), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.88/2.03  tff(c_770, plain, (![B_164, A_165]: (B_164=A_165 | ~r1_tarski(B_164, A_165) | ~r1_tarski(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.88/2.03  tff(c_792, plain, (![B_166]: (k1_tarski(B_166)='#skF_6' | ~r1_tarski(k1_tarski(B_166), '#skF_6'))), inference(resolution, [status(thm)], [c_536, c_770])).
% 4.88/2.03  tff(c_802, plain, (![A_167]: (k1_tarski(A_167)='#skF_6' | ~r2_hidden(A_167, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_792])).
% 4.88/2.03  tff(c_812, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_6, c_802])).
% 4.88/2.03  tff(c_813, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_812])).
% 4.88/2.03  tff(c_743, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158, B_159), A_158) | r1_tarski(A_158, B_159))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.88/2.03  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/2.03  tff(c_759, plain, (![A_160, B_161]: (~v1_xboole_0(A_160) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_743, c_4])).
% 4.88/2.03  tff(c_24, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.88/2.03  tff(c_768, plain, (![A_160, B_161]: (k2_xboole_0(A_160, B_161)=B_161 | ~v1_xboole_0(A_160))), inference(resolution, [status(thm)], [c_759, c_24])).
% 4.88/2.03  tff(c_825, plain, (![B_161]: (k2_xboole_0('#skF_6', B_161)=B_161)), inference(resolution, [status(thm)], [c_813, c_768])).
% 4.88/2.03  tff(c_827, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_825, c_80])).
% 4.88/2.03  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_827])).
% 4.88/2.03  tff(c_830, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_812])).
% 4.88/2.03  tff(c_711, plain, (![A_150, B_151]: (r2_hidden(A_150, B_151) | ~r1_tarski(k1_tarski(A_150), B_151))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.88/2.03  tff(c_724, plain, (![A_150, B_23]: (r2_hidden(A_150, k2_xboole_0(k1_tarski(A_150), B_23)))), inference(resolution, [status(thm)], [c_28, c_711])).
% 4.88/2.03  tff(c_940, plain, (![B_179]: (r2_hidden('#skF_1'('#skF_6'), k2_xboole_0('#skF_6', B_179)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_724])).
% 4.88/2.03  tff(c_957, plain, (![B_180]: (r2_hidden('#skF_1'('#skF_6'), k1_tarski(B_180)))), inference(superposition, [status(thm), theory('equality')], [c_655, c_940])).
% 4.88/2.03  tff(c_36, plain, (![C_34, A_30]: (C_34=A_30 | ~r2_hidden(C_34, k1_tarski(A_30)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.88/2.03  tff(c_1080, plain, ('#skF_1'('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_957, c_36])).
% 4.88/2.03  tff(c_1081, plain, (k1_tarski('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1080, c_830])).
% 4.88/2.03  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1081])).
% 4.88/2.03  tff(c_1252, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 4.88/2.03  tff(c_1253, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 4.88/2.03  tff(c_78, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.88/2.03  tff(c_1380, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_1253, c_78])).
% 4.88/2.03  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.88/2.03  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.88/2.03  tff(c_32, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.88/2.03  tff(c_3067, plain, (![A_2657, B_2658]: (k5_xboole_0(k5_xboole_0(A_2657, B_2658), k2_xboole_0(A_2657, B_2658))=k3_xboole_0(A_2657, B_2658))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.88/2.03  tff(c_3149, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, A_27))=k3_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3067])).
% 4.88/2.03  tff(c_3159, plain, (![A_27]: (k5_xboole_0(k1_xboole_0, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_3149])).
% 4.88/2.03  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.88/2.03  tff(c_2641, plain, (![A_2644, B_2645, C_2646]: (k5_xboole_0(k5_xboole_0(A_2644, B_2645), C_2646)=k5_xboole_0(A_2644, k5_xboole_0(B_2645, C_2646)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.88/2.03  tff(c_2884, plain, (![A_2653, C_2654]: (k5_xboole_0(A_2653, k5_xboole_0(A_2653, C_2654))=k5_xboole_0(k1_xboole_0, C_2654))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2641])).
% 4.88/2.03  tff(c_2956, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=k5_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2884])).
% 4.88/2.03  tff(c_3392, plain, (![A_2663, B_2664]: (k5_xboole_0(A_2663, k5_xboole_0(B_2664, A_2663))=B_2664)), inference(demodulation, [status(thm), theory('equality')], [c_3159, c_2956])).
% 4.88/2.03  tff(c_3161, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_3159, c_2956])).
% 4.88/2.03  tff(c_3395, plain, (![B_2664, A_2663]: (k5_xboole_0(k5_xboole_0(B_2664, A_2663), B_2664)=A_2663)), inference(superposition, [status(thm), theory('equality')], [c_3392, c_3161])).
% 4.88/2.03  tff(c_1268, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_80])).
% 4.88/2.03  tff(c_3146, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1268, c_3067])).
% 4.88/2.03  tff(c_4368, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3395, c_3146])).
% 4.88/2.03  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.88/2.03  tff(c_2080, plain, (![B_2614, A_2615]: (k1_tarski(B_2614)=A_2615 | k1_xboole_0=A_2615 | ~r1_tarski(A_2615, k1_tarski(B_2614)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.88/2.03  tff(c_2099, plain, (![A_2615]: (k1_tarski('#skF_5')=A_2615 | k1_xboole_0=A_2615 | ~r1_tarski(A_2615, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1253, c_2080])).
% 4.88/2.03  tff(c_2119, plain, (![A_2616]: (A_2616='#skF_6' | k1_xboole_0=A_2616 | ~r1_tarski(A_2616, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_2099])).
% 4.88/2.03  tff(c_2154, plain, (![B_21]: (k3_xboole_0('#skF_6', B_21)='#skF_6' | k3_xboole_0('#skF_6', B_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_2119])).
% 4.88/2.03  tff(c_4476, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_4368, c_2154])).
% 4.88/2.03  tff(c_4490, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4368, c_4476])).
% 4.88/2.03  tff(c_4492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1252, c_1380, c_4490])).
% 4.88/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/2.03  
% 4.88/2.03  Inference rules
% 4.88/2.03  ----------------------
% 4.88/2.03  #Ref     : 0
% 4.88/2.03  #Sup     : 920
% 4.88/2.03  #Fact    : 1
% 4.88/2.03  #Define  : 0
% 4.88/2.03  #Split   : 7
% 4.88/2.03  #Chain   : 0
% 4.88/2.03  #Close   : 0
% 4.88/2.03  
% 4.88/2.03  Ordering : KBO
% 4.88/2.03  
% 4.88/2.03  Simplification rules
% 4.88/2.03  ----------------------
% 4.88/2.03  #Subsume      : 104
% 4.88/2.03  #Demod        : 316
% 4.88/2.03  #Tautology    : 421
% 4.88/2.03  #SimpNegUnit  : 31
% 4.88/2.03  #BackRed      : 9
% 4.88/2.03  
% 4.88/2.03  #Partial instantiations: 2268
% 4.88/2.03  #Strategies tried      : 1
% 4.88/2.03  
% 4.88/2.03  Timing (in seconds)
% 4.88/2.03  ----------------------
% 4.88/2.03  Preprocessing        : 0.34
% 4.88/2.03  Parsing              : 0.18
% 4.88/2.03  CNF conversion       : 0.03
% 4.88/2.03  Main loop            : 0.83
% 4.88/2.03  Inferencing          : 0.37
% 4.88/2.03  Reduction            : 0.26
% 4.88/2.04  Demodulation         : 0.20
% 4.88/2.04  BG Simplification    : 0.03
% 4.88/2.04  Subsumption          : 0.11
% 4.88/2.04  Abstraction          : 0.04
% 4.88/2.04  MUC search           : 0.00
% 4.88/2.04  Cooper               : 0.00
% 4.88/2.04  Total                : 1.22
% 4.88/2.04  Index Insertion      : 0.00
% 4.88/2.04  Index Deletion       : 0.00
% 4.88/2.04  Index Matching       : 0.00
% 4.88/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
