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
% DateTime   : Thu Dec  3 10:14:14 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 187 expanded)
%              Number of leaves         :   49 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 354 expanded)
%              Number of equality atoms :   49 ( 104 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_114,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_122,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_30,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_131,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_122,c_30])).

tff(c_143,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_162,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_170,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_162])).

tff(c_173,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = B_82
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_170,c_173])).

tff(c_182,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_176])).

tff(c_197,plain,(
    ! [B_85,A_86] :
      ( k2_relat_1(k7_relat_1(B_85,A_86)) = k9_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_197])).

tff(c_213,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_206])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_20])).

tff(c_263,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_256])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k1_relat_1(B_23))
      | k11_relat_1(B_23,A_22) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_235,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_243,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_235])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_347,plain,(
    ! [B_116,C_117,A_118] :
      ( r2_hidden(k1_funct_1(B_116,C_117),A_118)
      | ~ r2_hidden(C_117,k1_relat_1(B_116))
      | ~ v1_funct_1(B_116)
      | ~ v5_relat_1(B_116,A_118)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_363,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_347,c_62])).

tff(c_370,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_243,c_70,c_363])).

tff(c_373,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_370])).

tff(c_376,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_263,c_373])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_376])).

tff(c_379,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_389,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_387,plain,(
    ! [A_13] : m1_subset_1('#skF_6',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_16])).

tff(c_60,plain,(
    ! [B_53,A_52,C_54] :
      ( k1_xboole_0 = B_53
      | k1_relset_1(A_52,B_53,C_54) = A_52
      | ~ v1_funct_2(C_54,A_52,B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_696,plain,(
    ! [B_182,A_183,C_184] :
      ( B_182 = '#skF_6'
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_60])).

tff(c_702,plain,(
    ! [B_185,A_186] :
      ( B_185 = '#skF_6'
      | k1_relset_1(A_186,B_185,'#skF_6') = A_186
      | ~ v1_funct_2('#skF_6',A_186,B_185) ) ),
    inference(resolution,[status(thm)],[c_387,c_696])).

tff(c_711,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_702])).

tff(c_718,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_711])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_64] :
      ( v1_xboole_0(A_64)
      | r2_hidden('#skF_1'(A_64),A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_97,plain,(
    ! [A_65] :
      ( ~ r1_tarski(A_65,'#skF_1'(A_65))
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_88,c_36])).

tff(c_102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_385,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_800,plain,(
    ! [D_211,A_212,B_213,C_214] :
      ( r2_hidden(k4_tarski(D_211,'#skF_3'(A_212,B_213,C_214,D_211)),C_214)
      | ~ r2_hidden(D_211,B_213)
      | k1_relset_1(B_213,A_212,C_214) != B_213
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(B_213,A_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_856,plain,(
    ! [C_217,D_218,B_219,A_220] :
      ( ~ v1_xboole_0(C_217)
      | ~ r2_hidden(D_218,B_219)
      | k1_relset_1(B_219,A_220,C_217) != B_219
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(B_219,A_220))) ) ),
    inference(resolution,[status(thm)],[c_800,c_2])).

tff(c_872,plain,(
    ! [C_221,A_222,A_223] :
      ( ~ v1_xboole_0(C_221)
      | k1_relset_1(A_222,A_223,C_221) != A_222
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,A_223)))
      | v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_4,c_856])).

tff(c_876,plain,(
    ! [A_222,A_223] :
      ( ~ v1_xboole_0('#skF_6')
      | k1_relset_1(A_222,A_223,'#skF_6') != A_222
      | v1_xboole_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_387,c_872])).

tff(c_888,plain,(
    ! [A_228,A_229] :
      ( k1_relset_1(A_228,A_229,'#skF_6') != A_228
      | v1_xboole_0(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_876])).

tff(c_892,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_888])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:53:26 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.44  
% 3.15/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.15/1.44  
% 3.15/1.44  %Foreground sorts:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Background operators:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Foreground operators:
% 3.15/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.15/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.15/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.44  
% 3.27/1.46  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.27/1.46  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.27/1.46  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.27/1.46  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.27/1.46  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.27/1.46  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.27/1.46  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.27/1.46  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.27/1.46  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.27/1.46  tff(f_91, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.27/1.46  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.27/1.46  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.27/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.27/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.27/1.46  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.27/1.46  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 3.27/1.46  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.27/1.46  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.27/1.46  tff(c_114, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.27/1.46  tff(c_122, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_114])).
% 3.27/1.46  tff(c_30, plain, (![A_26]: (k2_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.27/1.46  tff(c_131, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_122, c_30])).
% 3.27/1.46  tff(c_143, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_131])).
% 3.27/1.46  tff(c_162, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.27/1.46  tff(c_170, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_162])).
% 3.27/1.46  tff(c_173, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=B_82 | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.27/1.46  tff(c_176, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_170, c_173])).
% 3.27/1.46  tff(c_182, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_176])).
% 3.27/1.46  tff(c_197, plain, (![B_85, A_86]: (k2_relat_1(k7_relat_1(B_85, A_86))=k9_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.46  tff(c_206, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_182, c_197])).
% 3.27/1.46  tff(c_213, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_206])).
% 3.27/1.46  tff(c_20, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.27/1.46  tff(c_256, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_213, c_20])).
% 3.27/1.46  tff(c_263, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_256])).
% 3.27/1.46  tff(c_24, plain, (![A_22, B_23]: (r2_hidden(A_22, k1_relat_1(B_23)) | k11_relat_1(B_23, A_22)=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.46  tff(c_235, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.27/1.46  tff(c_243, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_235])).
% 3.27/1.46  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.27/1.46  tff(c_347, plain, (![B_116, C_117, A_118]: (r2_hidden(k1_funct_1(B_116, C_117), A_118) | ~r2_hidden(C_117, k1_relat_1(B_116)) | ~v1_funct_1(B_116) | ~v5_relat_1(B_116, A_118) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.27/1.46  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.27/1.46  tff(c_363, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_347, c_62])).
% 3.27/1.46  tff(c_370, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_243, c_70, c_363])).
% 3.27/1.46  tff(c_373, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_370])).
% 3.27/1.46  tff(c_376, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_263, c_373])).
% 3.27/1.46  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_376])).
% 3.27/1.46  tff(c_379, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_131])).
% 3.27/1.46  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.27/1.46  tff(c_389, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_64])).
% 3.27/1.46  tff(c_68, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.27/1.46  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.46  tff(c_387, plain, (![A_13]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_16])).
% 3.27/1.46  tff(c_60, plain, (![B_53, A_52, C_54]: (k1_xboole_0=B_53 | k1_relset_1(A_52, B_53, C_54)=A_52 | ~v1_funct_2(C_54, A_52, B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.27/1.46  tff(c_696, plain, (![B_182, A_183, C_184]: (B_182='#skF_6' | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_60])).
% 3.27/1.46  tff(c_702, plain, (![B_185, A_186]: (B_185='#skF_6' | k1_relset_1(A_186, B_185, '#skF_6')=A_186 | ~v1_funct_2('#skF_6', A_186, B_185))), inference(resolution, [status(thm)], [c_387, c_696])).
% 3.27/1.46  tff(c_711, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_68, c_702])).
% 3.27/1.46  tff(c_718, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_389, c_711])).
% 3.27/1.46  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.46  tff(c_88, plain, (![A_64]: (v1_xboole_0(A_64) | r2_hidden('#skF_1'(A_64), A_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.46  tff(c_36, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.46  tff(c_97, plain, (![A_65]: (~r1_tarski(A_65, '#skF_1'(A_65)) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_88, c_36])).
% 3.27/1.46  tff(c_102, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_97])).
% 3.27/1.46  tff(c_385, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_102])).
% 3.27/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.46  tff(c_800, plain, (![D_211, A_212, B_213, C_214]: (r2_hidden(k4_tarski(D_211, '#skF_3'(A_212, B_213, C_214, D_211)), C_214) | ~r2_hidden(D_211, B_213) | k1_relset_1(B_213, A_212, C_214)!=B_213 | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(B_213, A_212))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.27/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.46  tff(c_856, plain, (![C_217, D_218, B_219, A_220]: (~v1_xboole_0(C_217) | ~r2_hidden(D_218, B_219) | k1_relset_1(B_219, A_220, C_217)!=B_219 | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(B_219, A_220))))), inference(resolution, [status(thm)], [c_800, c_2])).
% 3.27/1.46  tff(c_872, plain, (![C_221, A_222, A_223]: (~v1_xboole_0(C_221) | k1_relset_1(A_222, A_223, C_221)!=A_222 | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, A_223))) | v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_4, c_856])).
% 3.27/1.46  tff(c_876, plain, (![A_222, A_223]: (~v1_xboole_0('#skF_6') | k1_relset_1(A_222, A_223, '#skF_6')!=A_222 | v1_xboole_0(A_222))), inference(resolution, [status(thm)], [c_387, c_872])).
% 3.27/1.46  tff(c_888, plain, (![A_228, A_229]: (k1_relset_1(A_228, A_229, '#skF_6')!=A_228 | v1_xboole_0(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_876])).
% 3.27/1.46  tff(c_892, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_718, c_888])).
% 3.27/1.46  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_892])).
% 3.27/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.46  
% 3.27/1.46  Inference rules
% 3.27/1.46  ----------------------
% 3.27/1.46  #Ref     : 0
% 3.27/1.46  #Sup     : 165
% 3.27/1.46  #Fact    : 0
% 3.27/1.46  #Define  : 0
% 3.27/1.46  #Split   : 3
% 3.27/1.46  #Chain   : 0
% 3.27/1.46  #Close   : 0
% 3.27/1.46  
% 3.27/1.46  Ordering : KBO
% 3.27/1.46  
% 3.27/1.46  Simplification rules
% 3.27/1.46  ----------------------
% 3.27/1.46  #Subsume      : 4
% 3.27/1.46  #Demod        : 92
% 3.27/1.46  #Tautology    : 81
% 3.27/1.46  #SimpNegUnit  : 3
% 3.27/1.46  #BackRed      : 10
% 3.27/1.46  
% 3.27/1.46  #Partial instantiations: 0
% 3.27/1.46  #Strategies tried      : 1
% 3.27/1.46  
% 3.27/1.46  Timing (in seconds)
% 3.27/1.46  ----------------------
% 3.27/1.46  Preprocessing        : 0.34
% 3.27/1.46  Parsing              : 0.18
% 3.27/1.46  CNF conversion       : 0.02
% 3.27/1.46  Main loop            : 0.36
% 3.27/1.46  Inferencing          : 0.13
% 3.27/1.46  Reduction            : 0.11
% 3.27/1.46  Demodulation         : 0.07
% 3.27/1.46  BG Simplification    : 0.02
% 3.27/1.46  Subsumption          : 0.06
% 3.27/1.46  Abstraction          : 0.02
% 3.27/1.46  MUC search           : 0.00
% 3.27/1.46  Cooper               : 0.00
% 3.27/1.46  Total                : 0.74
% 3.27/1.46  Index Insertion      : 0.00
% 3.27/1.46  Index Deletion       : 0.00
% 3.27/1.46  Index Matching       : 0.00
% 3.27/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
