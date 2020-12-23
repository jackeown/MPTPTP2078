%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:12 EST 2020

% Result     : Theorem 16.13s
% Output     : CNFRefutation 16.15s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 371 expanded)
%              Number of leaves         :   40 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 999 expanded)
%              Number of equality atoms :   98 ( 661 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_122,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_36])).

tff(c_654,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(B_118) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_668,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_127,c_654])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_102,c_668])).

tff(c_678,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_679,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_34,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_681,plain,(
    ! [A_18] : k5_xboole_0(A_18,'#skF_7') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_34])).

tff(c_714,plain,(
    ! [B_126,A_127] : k3_xboole_0(B_126,A_127) = k3_xboole_0(A_127,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_680,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_679,c_32])).

tff(c_730,plain,(
    ! [A_127] : k3_xboole_0('#skF_7',A_127) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_680])).

tff(c_957,plain,(
    ! [A_151,B_152] : k5_xboole_0(A_151,k3_xboole_0(A_151,B_152)) = k4_xboole_0(A_151,B_152) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_966,plain,(
    ! [A_127] : k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7',A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_957])).

tff(c_978,plain,(
    ! [A_127] : k4_xboole_0('#skF_7',A_127) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_966])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_847,plain,(
    ! [A_137,B_138] :
      ( r1_tarski(A_137,B_138)
      | k4_xboole_0(A_137,B_138) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_24])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1830,plain,(
    ! [A_5034,B_5035] :
      ( k2_xboole_0(A_5034,B_5035) = B_5035
      | k4_xboole_0(A_5034,B_5035) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_847,c_30])).

tff(c_1846,plain,(
    ! [A_127] : k2_xboole_0('#skF_7',A_127) = A_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_1830])).

tff(c_1862,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_84])).

tff(c_1864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_1862])).

tff(c_1866,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1998,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_1866,c_82])).

tff(c_1865,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1894,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_84])).

tff(c_2390,plain,(
    ! [D_5082,B_5083,A_5084] :
      ( ~ r2_hidden(D_5082,B_5083)
      | r2_hidden(D_5082,k2_xboole_0(A_5084,B_5083)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2414,plain,(
    ! [D_5082] :
      ( ~ r2_hidden(D_5082,'#skF_8')
      | r2_hidden(D_5082,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1894,c_2390])).

tff(c_56,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2842,plain,(
    ! [D_5110,B_5111,A_5112] :
      ( D_5110 = B_5111
      | D_5110 = A_5112
      | ~ r2_hidden(D_5110,k2_tarski(A_5112,B_5111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2861,plain,(
    ! [D_5113,A_5114] :
      ( D_5113 = A_5114
      | D_5113 = A_5114
      | ~ r2_hidden(D_5113,k1_tarski(A_5114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2842])).

tff(c_2903,plain,(
    ! [D_5116] :
      ( D_5116 = '#skF_6'
      | D_5116 = '#skF_6'
      | ~ r2_hidden(D_5116,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_2861])).

tff(c_2920,plain,(
    ! [D_5117] :
      ( D_5117 = '#skF_6'
      | ~ r2_hidden(D_5117,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2414,c_2903])).

tff(c_2924,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_2920])).

tff(c_2927,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1865,c_2924])).

tff(c_2931,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2927,c_22])).

tff(c_2934,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1865,c_2931])).

tff(c_21163,plain,(
    ! [A_59343,B_59344,C_59345] :
      ( r2_hidden('#skF_1'(A_59343,B_59344,C_59345),B_59344)
      | r2_hidden('#skF_1'(A_59343,B_59344,C_59345),A_59343)
      | r2_hidden('#skF_2'(A_59343,B_59344,C_59345),C_59345)
      | k2_xboole_0(A_59343,B_59344) = C_59345 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71138,plain,(
    ! [A_96002,B_96003] :
      ( r2_hidden('#skF_1'(A_96002,B_96003,A_96002),B_96003)
      | r2_hidden('#skF_2'(A_96002,B_96003,A_96002),A_96002)
      | k2_xboole_0(A_96002,B_96003) = A_96002 ) ),
    inference(resolution,[status(thm)],[c_21163,c_18])).

tff(c_71346,plain,(
    ! [B_96178] :
      ( r2_hidden('#skF_2'(B_96178,B_96178,B_96178),B_96178)
      | k2_xboole_0(B_96178,B_96178) = B_96178 ) ),
    inference(resolution,[status(thm)],[c_71138,c_18])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27095,plain,(
    ! [A_73250,C_73251] :
      ( ~ r2_hidden('#skF_2'(A_73250,A_73250,C_73251),A_73250)
      | k2_xboole_0(A_73250,A_73250) = C_73251
      | r2_hidden('#skF_1'(A_73250,A_73250,C_73251),A_73250) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_27198,plain,(
    ! [A_73250] :
      ( ~ r2_hidden('#skF_2'(A_73250,A_73250,A_73250),A_73250)
      | k2_xboole_0(A_73250,A_73250) = A_73250 ) ),
    inference(resolution,[status(thm)],[c_27095,c_14])).

tff(c_71439,plain,(
    ! [B_96178] : k2_xboole_0(B_96178,B_96178) = B_96178 ),
    inference(resolution,[status(thm)],[c_71346,c_27198])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21162,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k2_xboole_0(A_3,A_3) = C_5
      | r2_hidden('#skF_1'(A_3,A_3,C_5),A_3) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_20])).

tff(c_71860,plain,(
    ! [A_97751,C_97752] :
      ( r2_hidden('#skF_2'(A_97751,A_97751,C_97752),C_97752)
      | C_97752 = A_97751
      | r2_hidden('#skF_1'(A_97751,A_97751,C_97752),A_97751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71439,c_21162])).

tff(c_3871,plain,(
    ! [A_5181,B_5182,C_5183] :
      ( ~ r2_hidden('#skF_1'(A_5181,B_5182,C_5183),C_5183)
      | r2_hidden('#skF_2'(A_5181,B_5182,C_5183),C_5183)
      | k2_xboole_0(A_5181,B_5182) = C_5183 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3898,plain,(
    ! [A_5181,B_5182] :
      ( r2_hidden('#skF_2'(A_5181,B_5182,'#skF_7'),'#skF_7')
      | k2_xboole_0(A_5181,B_5182) = '#skF_7'
      | ~ r2_hidden('#skF_1'(A_5181,B_5182,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2414,c_3871])).

tff(c_71906,plain,
    ( k2_xboole_0('#skF_8','#skF_8') = '#skF_7'
    | r2_hidden('#skF_2'('#skF_8','#skF_8','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_71860,c_3898])).

tff(c_71957,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_2'('#skF_8','#skF_8','#skF_7'),'#skF_7')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71439,c_71906])).

tff(c_71958,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1998,c_1998,c_71957])).

tff(c_2871,plain,(
    ! [D_5113] :
      ( D_5113 = '#skF_6'
      | D_5113 = '#skF_6'
      | ~ r2_hidden(D_5113,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_2861])).

tff(c_71981,plain,(
    '#skF_2'('#skF_8','#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_71958,c_2871])).

tff(c_22093,plain,(
    ! [B_4,C_5] :
      ( ~ r2_hidden('#skF_2'(B_4,B_4,C_5),B_4)
      | k2_xboole_0(B_4,B_4) = C_5
      | r2_hidden('#skF_1'(B_4,B_4,C_5),B_4) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_71776,plain,(
    ! [B_4,C_5] :
      ( ~ r2_hidden('#skF_2'(B_4,B_4,C_5),B_4)
      | C_5 = B_4
      | r2_hidden('#skF_1'(B_4,B_4,C_5),B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71439,c_22093])).

tff(c_4202,plain,(
    ! [A_5194,B_5195,C_5196] :
      ( ~ r2_hidden('#skF_1'(A_5194,B_5195,C_5196),C_5196)
      | ~ r2_hidden('#skF_2'(A_5194,B_5195,C_5196),B_5195)
      | k2_xboole_0(A_5194,B_5195) = C_5196 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4223,plain,(
    ! [A_5194,B_5195] :
      ( ~ r2_hidden('#skF_2'(A_5194,B_5195,'#skF_7'),B_5195)
      | k2_xboole_0(A_5194,B_5195) = '#skF_7'
      | ~ r2_hidden('#skF_1'(A_5194,B_5195,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2414,c_4202])).

tff(c_71988,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | k2_xboole_0('#skF_8','#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_8','#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_71981,c_4223])).

tff(c_71994,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r2_hidden('#skF_1'('#skF_8','#skF_8','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71439,c_2934,c_71988])).

tff(c_71995,plain,(
    ~ r2_hidden('#skF_1'('#skF_8','#skF_8','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1998,c_71994])).

tff(c_72005,plain,
    ( ~ r2_hidden('#skF_2'('#skF_8','#skF_8','#skF_7'),'#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_71776,c_71995])).

tff(c_72021,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2934,c_71981,c_72005])).

tff(c_72023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1998,c_72021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.13/7.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.15/7.59  
% 16.15/7.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.15/7.59  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3
% 16.15/7.59  
% 16.15/7.59  %Foreground sorts:
% 16.15/7.59  
% 16.15/7.59  
% 16.15/7.59  %Background operators:
% 16.15/7.59  
% 16.15/7.59  
% 16.15/7.59  %Foreground operators:
% 16.15/7.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.15/7.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.15/7.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.15/7.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.15/7.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.15/7.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.15/7.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.15/7.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 16.15/7.59  tff('#skF_7', type, '#skF_7': $i).
% 16.15/7.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.15/7.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.15/7.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.15/7.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.15/7.59  tff('#skF_6', type, '#skF_6': $i).
% 16.15/7.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.15/7.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.15/7.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.15/7.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.15/7.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.15/7.59  tff('#skF_8', type, '#skF_8': $i).
% 16.15/7.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.15/7.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.15/7.59  tff('#skF_3', type, '#skF_3': $i > $i).
% 16.15/7.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.15/7.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.15/7.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.15/7.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.15/7.59  
% 16.15/7.61  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 16.15/7.61  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.15/7.61  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 16.15/7.61  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 16.15/7.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.15/7.61  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 16.15/7.61  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 16.15/7.61  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 16.15/7.61  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.15/7.61  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.15/7.61  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 16.15/7.61  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 16.15/7.61  tff(f_69, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 16.15/7.61  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.15/7.61  tff(c_122, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 16.15/7.61  tff(c_78, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.15/7.61  tff(c_102, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 16.15/7.61  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.15/7.61  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.15/7.61  tff(c_127, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_36])).
% 16.15/7.61  tff(c_654, plain, (![B_118, A_119]: (k1_tarski(B_118)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(B_118)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 16.15/7.61  tff(c_668, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_127, c_654])).
% 16.15/7.61  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_102, c_668])).
% 16.15/7.61  tff(c_678, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 16.15/7.61  tff(c_679, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 16.15/7.61  tff(c_34, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.15/7.61  tff(c_681, plain, (![A_18]: (k5_xboole_0(A_18, '#skF_7')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_679, c_34])).
% 16.15/7.61  tff(c_714, plain, (![B_126, A_127]: (k3_xboole_0(B_126, A_127)=k3_xboole_0(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.15/7.61  tff(c_32, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.15/7.61  tff(c_680, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_679, c_32])).
% 16.15/7.61  tff(c_730, plain, (![A_127]: (k3_xboole_0('#skF_7', A_127)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_714, c_680])).
% 16.15/7.61  tff(c_957, plain, (![A_151, B_152]: (k5_xboole_0(A_151, k3_xboole_0(A_151, B_152))=k4_xboole_0(A_151, B_152))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.15/7.61  tff(c_966, plain, (![A_127]: (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', A_127))), inference(superposition, [status(thm), theory('equality')], [c_730, c_957])).
% 16.15/7.61  tff(c_978, plain, (![A_127]: (k4_xboole_0('#skF_7', A_127)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_966])).
% 16.15/7.61  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.15/7.61  tff(c_847, plain, (![A_137, B_138]: (r1_tarski(A_137, B_138) | k4_xboole_0(A_137, B_138)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_24])).
% 16.15/7.61  tff(c_30, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.15/7.61  tff(c_1830, plain, (![A_5034, B_5035]: (k2_xboole_0(A_5034, B_5035)=B_5035 | k4_xboole_0(A_5034, B_5035)!='#skF_7')), inference(resolution, [status(thm)], [c_847, c_30])).
% 16.15/7.61  tff(c_1846, plain, (![A_127]: (k2_xboole_0('#skF_7', A_127)=A_127)), inference(superposition, [status(thm), theory('equality')], [c_978, c_1830])).
% 16.15/7.61  tff(c_1862, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_84])).
% 16.15/7.61  tff(c_1864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_678, c_1862])).
% 16.15/7.61  tff(c_1866, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 16.15/7.61  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 16.15/7.61  tff(c_1998, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_1866, c_82])).
% 16.15/7.61  tff(c_1865, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 16.15/7.61  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.15/7.61  tff(c_1894, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_84])).
% 16.15/7.61  tff(c_2390, plain, (![D_5082, B_5083, A_5084]: (~r2_hidden(D_5082, B_5083) | r2_hidden(D_5082, k2_xboole_0(A_5084, B_5083)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_2414, plain, (![D_5082]: (~r2_hidden(D_5082, '#skF_8') | r2_hidden(D_5082, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1894, c_2390])).
% 16.15/7.61  tff(c_56, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.15/7.61  tff(c_2842, plain, (![D_5110, B_5111, A_5112]: (D_5110=B_5111 | D_5110=A_5112 | ~r2_hidden(D_5110, k2_tarski(A_5112, B_5111)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.15/7.61  tff(c_2861, plain, (![D_5113, A_5114]: (D_5113=A_5114 | D_5113=A_5114 | ~r2_hidden(D_5113, k1_tarski(A_5114)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2842])).
% 16.15/7.61  tff(c_2903, plain, (![D_5116]: (D_5116='#skF_6' | D_5116='#skF_6' | ~r2_hidden(D_5116, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_2861])).
% 16.15/7.61  tff(c_2920, plain, (![D_5117]: (D_5117='#skF_6' | ~r2_hidden(D_5117, '#skF_8'))), inference(resolution, [status(thm)], [c_2414, c_2903])).
% 16.15/7.61  tff(c_2924, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_2920])).
% 16.15/7.61  tff(c_2927, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1865, c_2924])).
% 16.15/7.61  tff(c_2931, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2927, c_22])).
% 16.15/7.61  tff(c_2934, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1865, c_2931])).
% 16.15/7.61  tff(c_21163, plain, (![A_59343, B_59344, C_59345]: (r2_hidden('#skF_1'(A_59343, B_59344, C_59345), B_59344) | r2_hidden('#skF_1'(A_59343, B_59344, C_59345), A_59343) | r2_hidden('#skF_2'(A_59343, B_59344, C_59345), C_59345) | k2_xboole_0(A_59343, B_59344)=C_59345)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_71138, plain, (![A_96002, B_96003]: (r2_hidden('#skF_1'(A_96002, B_96003, A_96002), B_96003) | r2_hidden('#skF_2'(A_96002, B_96003, A_96002), A_96002) | k2_xboole_0(A_96002, B_96003)=A_96002)), inference(resolution, [status(thm)], [c_21163, c_18])).
% 16.15/7.61  tff(c_71346, plain, (![B_96178]: (r2_hidden('#skF_2'(B_96178, B_96178, B_96178), B_96178) | k2_xboole_0(B_96178, B_96178)=B_96178)), inference(resolution, [status(thm)], [c_71138, c_18])).
% 16.15/7.61  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_27095, plain, (![A_73250, C_73251]: (~r2_hidden('#skF_2'(A_73250, A_73250, C_73251), A_73250) | k2_xboole_0(A_73250, A_73250)=C_73251 | r2_hidden('#skF_1'(A_73250, A_73250, C_73251), A_73250))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 16.15/7.61  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_27198, plain, (![A_73250]: (~r2_hidden('#skF_2'(A_73250, A_73250, A_73250), A_73250) | k2_xboole_0(A_73250, A_73250)=A_73250)), inference(resolution, [status(thm)], [c_27095, c_14])).
% 16.15/7.61  tff(c_71439, plain, (![B_96178]: (k2_xboole_0(B_96178, B_96178)=B_96178)), inference(resolution, [status(thm)], [c_71346, c_27198])).
% 16.15/7.61  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_21162, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k2_xboole_0(A_3, A_3)=C_5 | r2_hidden('#skF_1'(A_3, A_3, C_5), A_3))), inference(factorization, [status(thm), theory('equality')], [c_20])).
% 16.15/7.61  tff(c_71860, plain, (![A_97751, C_97752]: (r2_hidden('#skF_2'(A_97751, A_97751, C_97752), C_97752) | C_97752=A_97751 | r2_hidden('#skF_1'(A_97751, A_97751, C_97752), A_97751))), inference(demodulation, [status(thm), theory('equality')], [c_71439, c_21162])).
% 16.15/7.61  tff(c_3871, plain, (![A_5181, B_5182, C_5183]: (~r2_hidden('#skF_1'(A_5181, B_5182, C_5183), C_5183) | r2_hidden('#skF_2'(A_5181, B_5182, C_5183), C_5183) | k2_xboole_0(A_5181, B_5182)=C_5183)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_3898, plain, (![A_5181, B_5182]: (r2_hidden('#skF_2'(A_5181, B_5182, '#skF_7'), '#skF_7') | k2_xboole_0(A_5181, B_5182)='#skF_7' | ~r2_hidden('#skF_1'(A_5181, B_5182, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_2414, c_3871])).
% 16.15/7.61  tff(c_71906, plain, (k2_xboole_0('#skF_8', '#skF_8')='#skF_7' | r2_hidden('#skF_2'('#skF_8', '#skF_8', '#skF_7'), '#skF_7') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_71860, c_3898])).
% 16.15/7.61  tff(c_71957, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_2'('#skF_8', '#skF_8', '#skF_7'), '#skF_7') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_71439, c_71906])).
% 16.15/7.61  tff(c_71958, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1998, c_1998, c_71957])).
% 16.15/7.61  tff(c_2871, plain, (![D_5113]: (D_5113='#skF_6' | D_5113='#skF_6' | ~r2_hidden(D_5113, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_2861])).
% 16.15/7.61  tff(c_71981, plain, ('#skF_2'('#skF_8', '#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_71958, c_2871])).
% 16.15/7.61  tff(c_22093, plain, (![B_4, C_5]: (~r2_hidden('#skF_2'(B_4, B_4, C_5), B_4) | k2_xboole_0(B_4, B_4)=C_5 | r2_hidden('#skF_1'(B_4, B_4, C_5), B_4))), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 16.15/7.61  tff(c_71776, plain, (![B_4, C_5]: (~r2_hidden('#skF_2'(B_4, B_4, C_5), B_4) | C_5=B_4 | r2_hidden('#skF_1'(B_4, B_4, C_5), B_4))), inference(demodulation, [status(thm), theory('equality')], [c_71439, c_22093])).
% 16.15/7.61  tff(c_4202, plain, (![A_5194, B_5195, C_5196]: (~r2_hidden('#skF_1'(A_5194, B_5195, C_5196), C_5196) | ~r2_hidden('#skF_2'(A_5194, B_5195, C_5196), B_5195) | k2_xboole_0(A_5194, B_5195)=C_5196)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.15/7.61  tff(c_4223, plain, (![A_5194, B_5195]: (~r2_hidden('#skF_2'(A_5194, B_5195, '#skF_7'), B_5195) | k2_xboole_0(A_5194, B_5195)='#skF_7' | ~r2_hidden('#skF_1'(A_5194, B_5195, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_2414, c_4202])).
% 16.15/7.61  tff(c_71988, plain, (~r2_hidden('#skF_6', '#skF_8') | k2_xboole_0('#skF_8', '#skF_8')='#skF_7' | ~r2_hidden('#skF_1'('#skF_8', '#skF_8', '#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_71981, c_4223])).
% 16.15/7.61  tff(c_71994, plain, ('#skF_7'='#skF_8' | ~r2_hidden('#skF_1'('#skF_8', '#skF_8', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71439, c_2934, c_71988])).
% 16.15/7.61  tff(c_71995, plain, (~r2_hidden('#skF_1'('#skF_8', '#skF_8', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1998, c_71994])).
% 16.15/7.61  tff(c_72005, plain, (~r2_hidden('#skF_2'('#skF_8', '#skF_8', '#skF_7'), '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_71776, c_71995])).
% 16.15/7.61  tff(c_72021, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2934, c_71981, c_72005])).
% 16.15/7.61  tff(c_72023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1998, c_72021])).
% 16.15/7.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.15/7.61  
% 16.15/7.61  Inference rules
% 16.15/7.61  ----------------------
% 16.15/7.61  #Ref     : 0
% 16.15/7.61  #Sup     : 12078
% 16.15/7.61  #Fact    : 22
% 16.15/7.61  #Define  : 0
% 16.15/7.61  #Split   : 16
% 16.15/7.61  #Chain   : 0
% 16.15/7.61  #Close   : 0
% 16.15/7.61  
% 16.15/7.61  Ordering : KBO
% 16.15/7.61  
% 16.15/7.61  Simplification rules
% 16.15/7.61  ----------------------
% 16.15/7.61  #Subsume      : 4787
% 16.15/7.61  #Demod        : 4766
% 16.15/7.61  #Tautology    : 1029
% 16.15/7.61  #SimpNegUnit  : 322
% 16.15/7.61  #BackRed      : 64
% 16.15/7.61  
% 16.15/7.61  #Partial instantiations: 35355
% 16.15/7.61  #Strategies tried      : 1
% 16.15/7.61  
% 16.15/7.61  Timing (in seconds)
% 16.15/7.61  ----------------------
% 16.15/7.61  Preprocessing        : 0.35
% 16.15/7.61  Parsing              : 0.18
% 16.15/7.61  CNF conversion       : 0.03
% 16.15/7.61  Main loop            : 6.46
% 16.15/7.61  Inferencing          : 2.06
% 16.15/7.61  Reduction            : 2.27
% 16.15/7.61  Demodulation         : 1.81
% 16.15/7.61  BG Simplification    : 0.20
% 16.15/7.61  Subsumption          : 1.65
% 16.15/7.61  Abstraction          : 0.39
% 16.15/7.61  MUC search           : 0.00
% 16.15/7.61  Cooper               : 0.00
% 16.15/7.61  Total                : 6.85
% 16.15/7.61  Index Insertion      : 0.00
% 16.15/7.61  Index Deletion       : 0.00
% 16.15/7.61  Index Matching       : 0.00
% 16.15/7.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
