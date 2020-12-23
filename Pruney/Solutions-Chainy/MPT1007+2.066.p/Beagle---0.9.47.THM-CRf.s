%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 261 expanded)
%              Number of leaves         :   44 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 ( 578 expanded)
%              Number of equality atoms :   35 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_95,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_103,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_243,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_251,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_243])).

tff(c_265,plain,(
    ! [A_97,B_98,C_99] :
      ( m1_subset_1(k2_relset_1(A_97,B_98,C_99),k1_zfmisc_1(B_98))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_265])).

tff(c_280,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_276])).

tff(c_28,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | r2_hidden(k4_tarski('#skF_2'(A_24),'#skF_3'(A_24)),A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_160,plain,(
    ! [B_77,C_78,A_79] :
      ( r2_hidden(B_77,k2_relat_1(C_78))
      | ~ r2_hidden(k4_tarski(A_79,B_77),C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_3'(A_83),k2_relat_1(A_83))
      | k1_xboole_0 = A_83
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_20,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2104,plain,(
    ! [A_359,A_360] :
      ( r2_hidden('#skF_3'(A_359),A_360)
      | ~ m1_subset_1(k2_relat_1(A_359),k1_zfmisc_1(A_360))
      | k1_xboole_0 = A_359
      | ~ v1_relat_1(A_359) ) ),
    inference(resolution,[status(thm)],[c_180,c_20])).

tff(c_2110,plain,
    ( r2_hidden('#skF_3'('#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_280,c_2104])).

tff(c_2119,plain,
    ( r2_hidden('#skF_3'('#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2110])).

tff(c_2123,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2119])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2139,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2140,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2123,c_30])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_637,plain,(
    ! [D_161,C_162,A_163,B_164] :
      ( r2_hidden(k1_funct_1(D_161,C_162),k2_relset_1(A_163,B_164,D_161))
      | k1_xboole_0 = B_164
      | ~ r2_hidden(C_162,A_163)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_2(D_161,A_163,B_164)
      | ~ v1_funct_1(D_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_645,plain,(
    ! [C_162] :
      ( r2_hidden(k1_funct_1('#skF_6',C_162),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_162,k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')))
      | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_637])).

tff(c_649,plain,(
    ! [C_162] :
      ( r2_hidden(k1_funct_1('#skF_6',C_162),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_162,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_645])).

tff(c_1946,plain,(
    ! [C_330] :
      ( r2_hidden(k1_funct_1('#skF_6',C_330),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_330,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_649])).

tff(c_36,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1953,plain,(
    ! [C_330] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_funct_1('#skF_6',C_330))
      | ~ r2_hidden(C_330,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1946,c_36])).

tff(c_2172,plain,(
    ! [C_330] :
      ( ~ r1_tarski('#skF_6',k1_funct_1('#skF_6',C_330))
      | ~ r2_hidden(C_330,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2140,c_1953])).

tff(c_2211,plain,(
    ! [C_367] : ~ r2_hidden(C_367,k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2139,c_2172])).

tff(c_2219,plain,(
    ! [A_19] :
      ( v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_19,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22,c_2211])).

tff(c_2265,plain,(
    ! [A_370] : ~ m1_subset_1(A_370,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_2219])).

tff(c_2270,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_2265])).

tff(c_2272,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2119])).

tff(c_137,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | r2_hidden(k4_tarski('#skF_2'(A_72),'#skF_3'(A_72)),A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2662,plain,(
    ! [A_418,A_419] :
      ( r2_hidden(k4_tarski('#skF_2'(A_418),'#skF_3'(A_418)),A_419)
      | ~ m1_subset_1(A_418,k1_zfmisc_1(A_419))
      | k1_xboole_0 = A_418
      | ~ v1_relat_1(A_418) ) ),
    inference(resolution,[status(thm)],[c_137,c_20])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2728,plain,(
    ! [C_423,A_424,D_425] :
      ( C_423 = '#skF_2'(A_424)
      | ~ m1_subset_1(A_424,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_423),D_425)))
      | k1_xboole_0 = A_424
      | ~ v1_relat_1(A_424) ) ),
    inference(resolution,[status(thm)],[c_2662,c_16])).

tff(c_2743,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_2728])).

tff(c_2758,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2743])).

tff(c_2759,plain,(
    '#skF_2'('#skF_6') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2272,c_2758])).

tff(c_170,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(A_80,k1_relat_1(C_81))
      | ~ r2_hidden(k4_tarski(A_80,B_82),C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_178,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_2'(A_24),k1_relat_1(A_24))
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_2775,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2759,c_178])).

tff(c_2791,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2775])).

tff(c_2792,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2272,c_2791])).

tff(c_297,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(k1_funct_1(B_103,A_104),k2_relat_1(B_103))
      | ~ r2_hidden(A_104,k1_relat_1(B_103))
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3105,plain,(
    ! [B_458,A_459,A_460] :
      ( r2_hidden(k1_funct_1(B_458,A_459),A_460)
      | ~ m1_subset_1(k2_relat_1(B_458),k1_zfmisc_1(A_460))
      | ~ r2_hidden(A_459,k1_relat_1(B_458))
      | ~ v1_funct_1(B_458)
      | ~ v1_relat_1(B_458) ) ),
    inference(resolution,[status(thm)],[c_297,c_20])).

tff(c_3109,plain,(
    ! [A_459] :
      ( r2_hidden(k1_funct_1('#skF_6',A_459),'#skF_5')
      | ~ r2_hidden(A_459,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_280,c_3105])).

tff(c_3120,plain,(
    ! [A_461] :
      ( r2_hidden(k1_funct_1('#skF_6',A_461),'#skF_5')
      | ~ r2_hidden(A_461,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_3109])).

tff(c_46,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3130,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3120,c_46])).

tff(c_3137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2792,c_3130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.97  
% 5.10/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.97  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 5.10/1.97  
% 5.10/1.97  %Foreground sorts:
% 5.10/1.97  
% 5.10/1.97  
% 5.10/1.97  %Background operators:
% 5.10/1.97  
% 5.10/1.97  
% 5.10/1.97  %Foreground operators:
% 5.10/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.10/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.97  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.10/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.10/1.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.10/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.10/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.10/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.10/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.10/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.10/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.10/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.10/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.97  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.10/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.97  
% 5.45/1.99  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.45/1.99  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.45/1.99  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.45/1.99  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.45/1.99  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.45/1.99  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.45/1.99  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.45/1.99  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 5.45/1.99  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 5.45/1.99  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.45/1.99  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.45/1.99  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.45/1.99  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.45/1.99  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.45/1.99  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 5.45/1.99  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 5.45/1.99  tff(c_18, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.45/1.99  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.45/1.99  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.45/1.99  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.45/1.99  tff(c_95, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.45/1.99  tff(c_103, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_95])).
% 5.45/1.99  tff(c_243, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.45/1.99  tff(c_251, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_243])).
% 5.45/1.99  tff(c_265, plain, (![A_97, B_98, C_99]: (m1_subset_1(k2_relset_1(A_97, B_98, C_99), k1_zfmisc_1(B_98)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.45/1.99  tff(c_276, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_251, c_265])).
% 5.45/1.99  tff(c_280, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_276])).
% 5.45/1.99  tff(c_28, plain, (![A_24]: (k1_xboole_0=A_24 | r2_hidden(k4_tarski('#skF_2'(A_24), '#skF_3'(A_24)), A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.45/1.99  tff(c_160, plain, (![B_77, C_78, A_79]: (r2_hidden(B_77, k2_relat_1(C_78)) | ~r2_hidden(k4_tarski(A_79, B_77), C_78) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.45/1.99  tff(c_180, plain, (![A_83]: (r2_hidden('#skF_3'(A_83), k2_relat_1(A_83)) | k1_xboole_0=A_83 | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_28, c_160])).
% 5.45/1.99  tff(c_20, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.45/1.99  tff(c_2104, plain, (![A_359, A_360]: (r2_hidden('#skF_3'(A_359), A_360) | ~m1_subset_1(k2_relat_1(A_359), k1_zfmisc_1(A_360)) | k1_xboole_0=A_359 | ~v1_relat_1(A_359))), inference(resolution, [status(thm)], [c_180, c_20])).
% 5.45/1.99  tff(c_2110, plain, (r2_hidden('#skF_3'('#skF_6'), '#skF_5') | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_280, c_2104])).
% 5.45/1.99  tff(c_2119, plain, (r2_hidden('#skF_3'('#skF_6'), '#skF_5') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2110])).
% 5.45/1.99  tff(c_2123, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2119])).
% 5.45/1.99  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.45/1.99  tff(c_2139, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2])).
% 5.45/1.99  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.45/1.99  tff(c_2140, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2123, c_2123, c_30])).
% 5.45/1.99  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.45/1.99  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.45/1.99  tff(c_52, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.45/1.99  tff(c_637, plain, (![D_161, C_162, A_163, B_164]: (r2_hidden(k1_funct_1(D_161, C_162), k2_relset_1(A_163, B_164, D_161)) | k1_xboole_0=B_164 | ~r2_hidden(C_162, A_163) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_2(D_161, A_163, B_164) | ~v1_funct_1(D_161))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.45/1.99  tff(c_645, plain, (![C_162]: (r2_hidden(k1_funct_1('#skF_6', C_162), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_162, k1_tarski('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))) | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_637])).
% 5.45/1.99  tff(c_649, plain, (![C_162]: (r2_hidden(k1_funct_1('#skF_6', C_162), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_162, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_645])).
% 5.45/1.99  tff(c_1946, plain, (![C_330]: (r2_hidden(k1_funct_1('#skF_6', C_330), k2_relat_1('#skF_6')) | ~r2_hidden(C_330, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_649])).
% 5.45/1.99  tff(c_36, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.45/1.99  tff(c_1953, plain, (![C_330]: (~r1_tarski(k2_relat_1('#skF_6'), k1_funct_1('#skF_6', C_330)) | ~r2_hidden(C_330, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_1946, c_36])).
% 5.45/1.99  tff(c_2172, plain, (![C_330]: (~r1_tarski('#skF_6', k1_funct_1('#skF_6', C_330)) | ~r2_hidden(C_330, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2140, c_1953])).
% 5.45/1.99  tff(c_2211, plain, (![C_367]: (~r2_hidden(C_367, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2139, c_2172])).
% 5.45/1.99  tff(c_2219, plain, (![A_19]: (v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_19, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_22, c_2211])).
% 5.45/1.99  tff(c_2265, plain, (![A_370]: (~m1_subset_1(A_370, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_10, c_2219])).
% 5.45/1.99  tff(c_2270, plain, $false, inference(resolution, [status(thm)], [c_18, c_2265])).
% 5.45/1.99  tff(c_2272, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2119])).
% 5.45/1.99  tff(c_137, plain, (![A_72]: (k1_xboole_0=A_72 | r2_hidden(k4_tarski('#skF_2'(A_72), '#skF_3'(A_72)), A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.45/1.99  tff(c_2662, plain, (![A_418, A_419]: (r2_hidden(k4_tarski('#skF_2'(A_418), '#skF_3'(A_418)), A_419) | ~m1_subset_1(A_418, k1_zfmisc_1(A_419)) | k1_xboole_0=A_418 | ~v1_relat_1(A_418))), inference(resolution, [status(thm)], [c_137, c_20])).
% 5.45/1.99  tff(c_16, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.45/1.99  tff(c_2728, plain, (![C_423, A_424, D_425]: (C_423='#skF_2'(A_424) | ~m1_subset_1(A_424, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_423), D_425))) | k1_xboole_0=A_424 | ~v1_relat_1(A_424))), inference(resolution, [status(thm)], [c_2662, c_16])).
% 5.45/1.99  tff(c_2743, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_2728])).
% 5.45/1.99  tff(c_2758, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2743])).
% 5.45/1.99  tff(c_2759, plain, ('#skF_2'('#skF_6')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2272, c_2758])).
% 5.45/1.99  tff(c_170, plain, (![A_80, C_81, B_82]: (r2_hidden(A_80, k1_relat_1(C_81)) | ~r2_hidden(k4_tarski(A_80, B_82), C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.45/1.99  tff(c_178, plain, (![A_24]: (r2_hidden('#skF_2'(A_24), k1_relat_1(A_24)) | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_28, c_170])).
% 5.45/1.99  tff(c_2775, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2759, c_178])).
% 5.45/1.99  tff(c_2791, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2775])).
% 5.45/1.99  tff(c_2792, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2272, c_2791])).
% 5.45/1.99  tff(c_297, plain, (![B_103, A_104]: (r2_hidden(k1_funct_1(B_103, A_104), k2_relat_1(B_103)) | ~r2_hidden(A_104, k1_relat_1(B_103)) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.45/1.99  tff(c_3105, plain, (![B_458, A_459, A_460]: (r2_hidden(k1_funct_1(B_458, A_459), A_460) | ~m1_subset_1(k2_relat_1(B_458), k1_zfmisc_1(A_460)) | ~r2_hidden(A_459, k1_relat_1(B_458)) | ~v1_funct_1(B_458) | ~v1_relat_1(B_458))), inference(resolution, [status(thm)], [c_297, c_20])).
% 5.45/1.99  tff(c_3109, plain, (![A_459]: (r2_hidden(k1_funct_1('#skF_6', A_459), '#skF_5') | ~r2_hidden(A_459, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_280, c_3105])).
% 5.45/1.99  tff(c_3120, plain, (![A_461]: (r2_hidden(k1_funct_1('#skF_6', A_461), '#skF_5') | ~r2_hidden(A_461, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_3109])).
% 5.45/1.99  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.45/1.99  tff(c_3130, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3120, c_46])).
% 5.45/1.99  tff(c_3137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2792, c_3130])).
% 5.45/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.45/1.99  
% 5.45/1.99  Inference rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Ref     : 0
% 5.45/1.99  #Sup     : 651
% 5.45/1.99  #Fact    : 0
% 5.45/1.99  #Define  : 0
% 5.45/1.99  #Split   : 29
% 5.45/1.99  #Chain   : 0
% 5.45/1.99  #Close   : 0
% 5.45/1.99  
% 5.45/1.99  Ordering : KBO
% 5.45/1.99  
% 5.45/1.99  Simplification rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Subsume      : 108
% 5.45/1.99  #Demod        : 295
% 5.45/1.99  #Tautology    : 120
% 5.45/1.99  #SimpNegUnit  : 38
% 5.45/1.99  #BackRed      : 57
% 5.45/1.99  
% 5.45/1.99  #Partial instantiations: 0
% 5.45/1.99  #Strategies tried      : 1
% 5.45/1.99  
% 5.45/1.99  Timing (in seconds)
% 5.45/1.99  ----------------------
% 5.45/1.99  Preprocessing        : 0.33
% 5.45/1.99  Parsing              : 0.18
% 5.45/1.99  CNF conversion       : 0.02
% 5.45/1.99  Main loop            : 0.89
% 5.45/1.99  Inferencing          : 0.32
% 5.45/1.99  Reduction            : 0.29
% 5.45/1.99  Demodulation         : 0.19
% 5.45/1.99  BG Simplification    : 0.03
% 5.45/1.99  Subsumption          : 0.17
% 5.45/1.99  Abstraction          : 0.04
% 5.45/1.99  MUC search           : 0.00
% 5.45/1.99  Cooper               : 0.00
% 5.45/1.99  Total                : 1.26
% 5.45/1.99  Index Insertion      : 0.00
% 5.45/1.99  Index Deletion       : 0.00
% 5.45/1.99  Index Matching       : 0.00
% 5.45/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
