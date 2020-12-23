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
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 368 expanded)
%              Number of leaves         :   46 ( 140 expanded)
%              Depth                    :   14
%              Number of atoms          :  185 ( 779 expanded)
%              Number of equality atoms :   73 ( 318 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_109,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_113,c_36])).

tff(c_122,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_163,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_167,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_163])).

tff(c_195,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_198,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_195])).

tff(c_201,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_198])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_24])).

tff(c_209,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_205])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k9_relat_1(A_15,k1_tarski(B_17)) = k11_relat_1(A_15,B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_230,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_22])).

tff(c_237,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_230])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,k1_relat_1(B_21))
      | k11_relat_1(B_21,A_20) = k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_283,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_287,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_283])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_288,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_56])).

tff(c_373,plain,(
    ! [B_108,A_109] :
      ( k2_relat_1(k7_relat_1(B_108,k1_tarski(A_109))) = k1_tarski(k1_funct_1(B_108,A_109))
      | ~ r2_hidden(A_109,k1_relat_1(B_108))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_388,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_2')) = k2_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_373])).

tff(c_396,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_2')) = k2_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_388])).

tff(c_397,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_396])).

tff(c_400,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_397])).

tff(c_403,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_237,c_400])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_403])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_412,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_406,c_34])).

tff(c_407,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_418,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_407])).

tff(c_658,plain,(
    ! [B_149,A_150] :
      ( k1_tarski(k1_funct_1(B_149,A_150)) = k2_relat_1(B_149)
      | k1_tarski(A_150) != k1_relat_1(B_149)
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_634,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_637,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_634])).

tff(c_639,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_637])).

tff(c_640,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_56])).

tff(c_664,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_640])).

tff(c_673,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_412,c_418,c_664])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_413,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_58])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_410,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_14])).

tff(c_573,plain,(
    ! [A_139,B_140] :
      ( r2_hidden(A_139,k1_relat_1(B_140))
      | k11_relat_1(B_140,A_139) = '#skF_4'
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_26])).

tff(c_588,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,'#skF_4')
      | k11_relat_1('#skF_4',A_139) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_573])).

tff(c_595,plain,(
    ! [A_141] :
      ( r2_hidden(A_141,'#skF_4')
      | k11_relat_1('#skF_4',A_141) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_588])).

tff(c_44,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_607,plain,(
    ! [A_141] :
      ( ~ r1_tarski('#skF_4',A_141)
      | k11_relat_1('#skF_4',A_141) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_595,c_44])).

tff(c_615,plain,(
    ! [A_141] : k11_relat_1('#skF_4',A_141) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_607])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k11_relat_1(B_21,A_20) != k1_xboole_0
      | ~ r2_hidden(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_554,plain,(
    ! [B_136,A_137] :
      ( k11_relat_1(B_136,A_137) != '#skF_4'
      | ~ r2_hidden(A_137,k1_relat_1(B_136))
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_28])).

tff(c_557,plain,(
    ! [A_137] :
      ( k11_relat_1('#skF_4',A_137) != '#skF_4'
      | ~ r2_hidden(A_137,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_554])).

tff(c_563,plain,(
    ! [A_137] :
      ( k11_relat_1('#skF_4',A_137) != '#skF_4'
      | ~ r2_hidden(A_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_557])).

tff(c_618,plain,(
    ! [A_137] : ~ r2_hidden(A_137,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_563])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_830,plain,(
    ! [D_169,C_170,A_171,B_172] :
      ( r2_hidden(k1_funct_1(D_169,C_170),k2_relset_1(A_171,B_172,D_169))
      | B_172 = '#skF_4'
      | ~ r2_hidden(C_170,A_171)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(D_169,A_171,B_172)
      | ~ v1_funct_1(D_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_54])).

tff(c_838,plain,(
    ! [C_170] :
      ( r2_hidden(k1_funct_1('#skF_4',C_170),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_170,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_830])).

tff(c_842,plain,(
    ! [C_170] :
      ( r2_hidden(k1_funct_1('#skF_4',C_170),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_170,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_838])).

tff(c_844,plain,(
    ! [C_173] : ~ r2_hidden(C_173,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_618,c_842])).

tff(c_855,plain,(
    ! [B_174] : r1_tarski(k1_tarski('#skF_2'),B_174) ),
    inference(resolution,[status(thm)],[c_6,c_844])).

tff(c_431,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_436,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_410,c_431])).

tff(c_870,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_855,c_436])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.52  
% 3.02/1.52  %Foreground sorts:
% 3.02/1.52  
% 3.02/1.52  
% 3.02/1.52  %Background operators:
% 3.02/1.52  
% 3.02/1.52  
% 3.02/1.52  %Foreground operators:
% 3.02/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.02/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.02/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.52  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.02/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.02/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.02/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.02/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.52  
% 3.21/1.54  tff(f_138, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.21/1.54  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.54  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.21/1.54  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.54  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.21/1.54  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.21/1.54  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.21/1.54  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.21/1.54  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.54  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 3.21/1.54  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.21/1.54  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.21/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.54  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.54  tff(f_100, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.21/1.54  tff(f_126, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.21/1.54  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.54  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.21/1.54  tff(c_109, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.54  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_109])).
% 3.21/1.54  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.21/1.54  tff(c_36, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.54  tff(c_120, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_113, c_36])).
% 3.21/1.54  tff(c_122, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 3.21/1.54  tff(c_163, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.21/1.54  tff(c_167, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_163])).
% 3.21/1.54  tff(c_195, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.54  tff(c_198, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_167, c_195])).
% 3.21/1.54  tff(c_201, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_198])).
% 3.21/1.54  tff(c_24, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.21/1.54  tff(c_205, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_201, c_24])).
% 3.21/1.54  tff(c_209, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_205])).
% 3.21/1.54  tff(c_22, plain, (![A_15, B_17]: (k9_relat_1(A_15, k1_tarski(B_17))=k11_relat_1(A_15, B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.54  tff(c_230, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_209, c_22])).
% 3.21/1.54  tff(c_237, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_230])).
% 3.21/1.54  tff(c_26, plain, (![A_20, B_21]: (r2_hidden(A_20, k1_relat_1(B_21)) | k11_relat_1(B_21, A_20)=k1_xboole_0 | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.54  tff(c_283, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.21/1.54  tff(c_287, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_283])).
% 3.21/1.54  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.21/1.54  tff(c_288, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_56])).
% 3.21/1.54  tff(c_373, plain, (![B_108, A_109]: (k2_relat_1(k7_relat_1(B_108, k1_tarski(A_109)))=k1_tarski(k1_funct_1(B_108, A_109)) | ~r2_hidden(A_109, k1_relat_1(B_108)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.21/1.54  tff(c_388, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))=k2_relat_1('#skF_4') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_201, c_373])).
% 3.21/1.54  tff(c_396, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))=k2_relat_1('#skF_4') | ~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_388])).
% 3.21/1.54  tff(c_397, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_288, c_396])).
% 3.21/1.54  tff(c_400, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_397])).
% 3.21/1.54  tff(c_403, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_113, c_237, c_400])).
% 3.21/1.54  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_403])).
% 3.21/1.54  tff(c_406, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_120])).
% 3.21/1.54  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.21/1.54  tff(c_412, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_406, c_34])).
% 3.21/1.54  tff(c_407, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 3.21/1.54  tff(c_418, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_407])).
% 3.21/1.54  tff(c_658, plain, (![B_149, A_150]: (k1_tarski(k1_funct_1(B_149, A_150))=k2_relat_1(B_149) | k1_tarski(A_150)!=k1_relat_1(B_149) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.21/1.54  tff(c_634, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.21/1.54  tff(c_637, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_634])).
% 3.21/1.54  tff(c_639, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_418, c_637])).
% 3.21/1.54  tff(c_640, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_56])).
% 3.21/1.54  tff(c_664, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_658, c_640])).
% 3.21/1.54  tff(c_673, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_412, c_418, c_664])).
% 3.21/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.54  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.21/1.54  tff(c_413, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_58])).
% 3.21/1.54  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.21/1.54  tff(c_410, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_14])).
% 3.21/1.54  tff(c_573, plain, (![A_139, B_140]: (r2_hidden(A_139, k1_relat_1(B_140)) | k11_relat_1(B_140, A_139)='#skF_4' | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_26])).
% 3.21/1.54  tff(c_588, plain, (![A_139]: (r2_hidden(A_139, '#skF_4') | k11_relat_1('#skF_4', A_139)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_573])).
% 3.21/1.54  tff(c_595, plain, (![A_141]: (r2_hidden(A_141, '#skF_4') | k11_relat_1('#skF_4', A_141)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_588])).
% 3.21/1.54  tff(c_44, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.54  tff(c_607, plain, (![A_141]: (~r1_tarski('#skF_4', A_141) | k11_relat_1('#skF_4', A_141)='#skF_4')), inference(resolution, [status(thm)], [c_595, c_44])).
% 3.21/1.54  tff(c_615, plain, (![A_141]: (k11_relat_1('#skF_4', A_141)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_607])).
% 3.21/1.54  tff(c_28, plain, (![B_21, A_20]: (k11_relat_1(B_21, A_20)!=k1_xboole_0 | ~r2_hidden(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.21/1.54  tff(c_554, plain, (![B_136, A_137]: (k11_relat_1(B_136, A_137)!='#skF_4' | ~r2_hidden(A_137, k1_relat_1(B_136)) | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_28])).
% 3.21/1.54  tff(c_557, plain, (![A_137]: (k11_relat_1('#skF_4', A_137)!='#skF_4' | ~r2_hidden(A_137, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_554])).
% 3.21/1.54  tff(c_563, plain, (![A_137]: (k11_relat_1('#skF_4', A_137)!='#skF_4' | ~r2_hidden(A_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_557])).
% 3.21/1.54  tff(c_618, plain, (![A_137]: (~r2_hidden(A_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_563])).
% 3.21/1.54  tff(c_62, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.21/1.54  tff(c_54, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.21/1.54  tff(c_830, plain, (![D_169, C_170, A_171, B_172]: (r2_hidden(k1_funct_1(D_169, C_170), k2_relset_1(A_171, B_172, D_169)) | B_172='#skF_4' | ~r2_hidden(C_170, A_171) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(D_169, A_171, B_172) | ~v1_funct_1(D_169))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_54])).
% 3.21/1.54  tff(c_838, plain, (![C_170]: (r2_hidden(k1_funct_1('#skF_4', C_170), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_170, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_639, c_830])).
% 3.21/1.54  tff(c_842, plain, (![C_170]: (r2_hidden(k1_funct_1('#skF_4', C_170), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_170, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_838])).
% 3.21/1.54  tff(c_844, plain, (![C_173]: (~r2_hidden(C_173, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_413, c_618, c_842])).
% 3.21/1.54  tff(c_855, plain, (![B_174]: (r1_tarski(k1_tarski('#skF_2'), B_174))), inference(resolution, [status(thm)], [c_6, c_844])).
% 3.21/1.54  tff(c_431, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.54  tff(c_436, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_410, c_431])).
% 3.21/1.54  tff(c_870, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_855, c_436])).
% 3.21/1.54  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_673, c_870])).
% 3.21/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.54  
% 3.21/1.54  Inference rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Ref     : 0
% 3.21/1.54  #Sup     : 172
% 3.21/1.54  #Fact    : 0
% 3.21/1.54  #Define  : 0
% 3.21/1.54  #Split   : 3
% 3.21/1.54  #Chain   : 0
% 3.21/1.54  #Close   : 0
% 3.21/1.54  
% 3.21/1.54  Ordering : KBO
% 3.21/1.54  
% 3.21/1.54  Simplification rules
% 3.21/1.54  ----------------------
% 3.21/1.54  #Subsume      : 11
% 3.21/1.54  #Demod        : 102
% 3.21/1.54  #Tautology    : 104
% 3.21/1.54  #SimpNegUnit  : 5
% 3.21/1.54  #BackRed      : 9
% 3.21/1.54  
% 3.21/1.54  #Partial instantiations: 0
% 3.21/1.54  #Strategies tried      : 1
% 3.21/1.54  
% 3.21/1.54  Timing (in seconds)
% 3.21/1.54  ----------------------
% 3.30/1.54  Preprocessing        : 0.37
% 3.30/1.54  Parsing              : 0.20
% 3.30/1.54  CNF conversion       : 0.02
% 3.30/1.54  Main loop            : 0.34
% 3.30/1.54  Inferencing          : 0.12
% 3.30/1.54  Reduction            : 0.10
% 3.30/1.54  Demodulation         : 0.07
% 3.30/1.54  BG Simplification    : 0.02
% 3.30/1.54  Subsumption          : 0.06
% 3.30/1.54  Abstraction          : 0.02
% 3.30/1.54  MUC search           : 0.00
% 3.30/1.54  Cooper               : 0.00
% 3.30/1.55  Total                : 0.74
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.55  Index Deletion       : 0.00
% 3.30/1.55  Index Matching       : 0.00
% 3.30/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
