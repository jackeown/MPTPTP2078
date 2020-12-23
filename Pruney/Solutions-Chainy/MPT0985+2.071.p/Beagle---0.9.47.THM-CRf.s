%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  322 (17332 expanded)
%              Number of leaves         :   44 (5403 expanded)
%              Depth                    :   21
%              Number of atoms          :  515 (43669 expanded)
%              Number of equality atoms :  200 (11071 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_158,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_146,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_88,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_92,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_10852,plain,(
    ! [C_884,A_885,B_886] :
      ( v1_relat_1(C_884)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_885,B_886))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10878,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_10852])).

tff(c_96,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_90,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_12004,plain,(
    ! [A_991,B_992,C_993] :
      ( k2_relset_1(A_991,B_992,C_993) = k2_relat_1(C_993)
      | ~ m1_subset_1(C_993,k1_zfmisc_1(k2_zfmisc_1(A_991,B_992))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12016,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_12004])).

tff(c_12031,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12016])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_185,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_188,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_191,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_188])).

tff(c_193,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_199,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_193])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_199])).

tff(c_214,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_306,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_323,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_306])).

tff(c_1559,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_relset_1(A_217,B_218,C_219) = k2_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1571,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_1559])).

tff(c_1586,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1571])).

tff(c_26,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) = k1_xboole_0
      | k2_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_333,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_323,c_26])).

tff(c_342,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_1589,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_342])).

tff(c_94,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1399,plain,(
    ! [A_202,B_203,C_204] :
      ( k1_relset_1(A_202,B_203,C_204) = k1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1421,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_1399])).

tff(c_1783,plain,(
    ! [B_239,A_240,C_241] :
      ( k1_xboole_0 = B_239
      | k1_relset_1(A_240,B_239,C_241) = A_240
      | ~ v1_funct_2(C_241,A_240,B_239)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1798,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_1783])).

tff(c_1821,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1421,c_1798])).

tff(c_1822,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1589,c_1821])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(k2_funct_1(A_23)) = k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_215,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1353,plain,(
    ! [A_198] :
      ( k2_relat_1(k2_funct_1(A_198)) = k1_relat_1(A_198)
      | ~ v2_funct_1(A_198)
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [A_43] :
      ( v1_funct_2(A_43,k1_relat_1(A_43),k2_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2987,plain,(
    ! [A_304] :
      ( v1_funct_2(k2_funct_1(A_304),k1_relat_1(k2_funct_1(A_304)),k1_relat_1(A_304))
      | ~ v1_funct_1(k2_funct_1(A_304))
      | ~ v1_relat_1(k2_funct_1(A_304))
      | ~ v2_funct_1(A_304)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_82])).

tff(c_2996,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_2987])).

tff(c_3011,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_96,c_90,c_215,c_2996])).

tff(c_3014,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3017,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_3014])).

tff(c_3021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_96,c_3017])).

tff(c_3023,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_1477,plain,(
    ! [A_214] :
      ( m1_subset_1(A_214,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_214),k2_relat_1(A_214))))
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3407,plain,(
    ! [A_340] :
      ( m1_subset_1(k2_funct_1(A_340),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_340),k2_relat_1(k2_funct_1(A_340)))))
      | ~ v1_funct_1(k2_funct_1(A_340))
      | ~ v1_relat_1(k2_funct_1(A_340))
      | ~ v2_funct_1(A_340)
      | ~ v1_funct_1(A_340)
      | ~ v1_relat_1(A_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1477])).

tff(c_3441,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_3407])).

tff(c_3470,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_96,c_90,c_3023,c_215,c_3441])).

tff(c_3504,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3470])).

tff(c_3522,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_96,c_90,c_1822,c_3504])).

tff(c_3524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_3522])).

tff(c_3526,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_4553,plain,(
    ! [A_442,B_443,C_444] :
      ( k2_relset_1(A_442,B_443,C_444) = k2_relat_1(C_444)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4566,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_4553])).

tff(c_4581,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3526,c_4566])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4614,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_6])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4611,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4581,c_4581,c_14])).

tff(c_255,plain,(
    ! [B_80,A_81] :
      ( v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_272,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_92,c_255])).

tff(c_334,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_4770,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_334])).

tff(c_4774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4614,c_4770])).

tff(c_4776,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_4775,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4780,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4775,c_8])).

tff(c_6050,plain,(
    ! [A_554] :
      ( A_554 = '#skF_5'
      | ~ v1_xboole_0(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_8])).

tff(c_6057,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4776,c_6050])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6470,plain,(
    ! [B_588,A_589] :
      ( B_588 = '#skF_5'
      | A_589 = '#skF_5'
      | k2_zfmisc_1(A_589,B_588) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_4780,c_12])).

tff(c_6480,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6057,c_6470])).

tff(c_6485,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6480])).

tff(c_4838,plain,(
    ! [A_458] :
      ( A_458 = '#skF_5'
      | ~ v1_xboole_0(A_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_8])).

tff(c_4845,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4776,c_4838])).

tff(c_5202,plain,(
    ! [B_490,A_491] :
      ( B_490 = '#skF_5'
      | A_491 = '#skF_5'
      | k2_zfmisc_1(A_491,B_490) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_4780,c_12])).

tff(c_5212,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4845,c_5202])).

tff(c_5217,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5212])).

tff(c_28,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = k1_xboole_0
      | k1_relat_1(A_20) != k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_332,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_323,c_28])).

tff(c_4836,plain,
    ( k2_relat_1('#skF_5') = '#skF_5'
    | k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_332])).

tff(c_4837,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4836])).

tff(c_5236,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5217,c_4837])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4790,plain,(
    ! [A_13] : m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_20])).

tff(c_5233,plain,(
    ! [A_13] : m1_subset_1('#skF_3',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_4790])).

tff(c_5369,plain,(
    ! [A_501,B_502,C_503] :
      ( k1_relset_1(A_501,B_502,C_503) = k1_relat_1(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_501,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5622,plain,(
    ! [A_523,B_524] : k1_relset_1(A_523,B_524,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5233,c_5369])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4848,plain,(
    ! [B_459] : k2_zfmisc_1('#skF_5',B_459) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_16])).

tff(c_76,plain,(
    ! [A_39,B_40] : m1_subset_1('#skF_2'(A_39,B_40),k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5036,plain,(
    ! [B_476] : m1_subset_1('#skF_2'('#skF_5',B_476),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4848,c_76])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5044,plain,(
    ! [B_476] :
      ( v1_xboole_0('#skF_2'('#skF_5',B_476))
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5036,c_22])).

tff(c_5055,plain,(
    ! [B_477] : v1_xboole_0('#skF_2'('#skF_5',B_477)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4775,c_5044])).

tff(c_4792,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_8])).

tff(c_5062,plain,(
    ! [B_477] : '#skF_2'('#skF_5',B_477) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5055,c_4792])).

tff(c_5224,plain,(
    ! [B_477] : '#skF_2'('#skF_3',B_477) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_5217,c_5062])).

tff(c_66,plain,(
    ! [A_39,B_40] : v1_funct_2('#skF_2'(A_39,B_40),A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5240,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5217,c_4780])).

tff(c_58,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_102,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_5566,plain,(
    ! [B_517,C_518] :
      ( k1_relset_1('#skF_3',B_517,C_518) = '#skF_3'
      | ~ v1_funct_2(C_518,'#skF_3',B_517)
      | ~ m1_subset_1(C_518,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5240,c_5240,c_5240,c_5240,c_102])).

tff(c_5574,plain,(
    ! [B_40] :
      ( k1_relset_1('#skF_3',B_40,'#skF_2'('#skF_3',B_40)) = '#skF_3'
      | ~ m1_subset_1('#skF_2'('#skF_3',B_40),k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_66,c_5566])).

tff(c_5583,plain,(
    ! [B_40] : k1_relset_1('#skF_3',B_40,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5233,c_5224,c_5224,c_5574])).

tff(c_5627,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_5583])).

tff(c_5634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5236,c_5627])).

tff(c_5635,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5212])).

tff(c_4924,plain,
    ( k1_relat_1('#skF_5') = '#skF_5'
    | k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_333])).

tff(c_4925,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4837,c_4924])).

tff(c_5648,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5635,c_5635,c_4925])).

tff(c_5734,plain,(
    ! [A_534] : m1_subset_1('#skF_4',k1_zfmisc_1(A_534)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5635,c_4790])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(A_32,B_33,C_34) = k2_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6028,plain,(
    ! [A_552,B_553] : k2_relset_1(A_552,B_553,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5734,c_48])).

tff(c_5664,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5635,c_88])).

tff(c_6032,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6028,c_5664])).

tff(c_6039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5648,c_6032])).

tff(c_6040,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4836])).

tff(c_6506,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_6485,c_6040])).

tff(c_6503,plain,(
    ! [A_13] : m1_subset_1('#skF_3',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_4790])).

tff(c_6826,plain,(
    ! [A_607,B_608,C_609] :
      ( k2_relset_1(A_607,B_608,C_609) = k2_relat_1(C_609)
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6836,plain,(
    ! [A_607,B_608] : k2_relset_1(A_607,B_608,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6503,c_6826])).

tff(c_6862,plain,(
    ! [A_612,B_613] : k2_relset_1(A_612,B_613,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6506,c_6836])).

tff(c_6515,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_88])).

tff(c_6866,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6862,c_6515])).

tff(c_4791,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_14])).

tff(c_6501,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_6485,c_4791])).

tff(c_6513,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_254])).

tff(c_6800,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6501,c_6513])).

tff(c_6877,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6866,c_6800])).

tff(c_6512,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_323])).

tff(c_6898,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6512])).

tff(c_6518,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_96])).

tff(c_6896,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6518])).

tff(c_6517,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_90])).

tff(c_6897,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6517])).

tff(c_6514,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_215])).

tff(c_6893,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6514])).

tff(c_6041,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4836])).

tff(c_6505,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_6485,c_6041])).

tff(c_6891,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6866,c_6505])).

tff(c_6420,plain,(
    ! [A_585] :
      ( k2_relat_1(k2_funct_1(A_585)) = k1_relat_1(A_585)
      | ~ v2_funct_1(A_585)
      | ~ v1_funct_1(A_585)
      | ~ v1_relat_1(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8743,plain,(
    ! [A_744] :
      ( v1_funct_2(k2_funct_1(A_744),k1_relat_1(k2_funct_1(A_744)),k1_relat_1(A_744))
      | ~ v1_funct_1(k2_funct_1(A_744))
      | ~ v1_relat_1(k2_funct_1(A_744))
      | ~ v2_funct_1(A_744)
      | ~ v1_funct_1(A_744)
      | ~ v1_relat_1(A_744) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6420,c_82])).

tff(c_8752,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6891,c_8743])).

tff(c_8764,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6898,c_6896,c_6897,c_6893,c_8752])).

tff(c_8765,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8764])).

tff(c_8768,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_8765])).

tff(c_8772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6898,c_6896,c_8768])).

tff(c_8774,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8764])).

tff(c_6880,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6866,c_6501])).

tff(c_6889,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6866,c_6506])).

tff(c_4785,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = '#skF_5'
      | k1_relat_1(A_20) != '#skF_5'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_28])).

tff(c_6488,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = '#skF_3'
      | k1_relat_1(A_20) != '#skF_3'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_6485,c_4785])).

tff(c_7303,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) = '#skF_4'
      | k1_relat_1(A_20) != '#skF_4'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6866,c_6866,c_6488])).

tff(c_8782,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_8774,c_7303])).

tff(c_8797,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8782])).

tff(c_8800,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8797])).

tff(c_8803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6898,c_6896,c_6897,c_6889,c_8800])).

tff(c_8804,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8782])).

tff(c_80,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_8827,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8804,c_80])).

tff(c_8857,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8774,c_6893,c_6880,c_8827])).

tff(c_8859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6877,c_8857])).

tff(c_8860,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6480])).

tff(c_4789,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_16])).

tff(c_8878,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_8860,c_4789])).

tff(c_8889,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_254])).

tff(c_9106,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8878,c_8889])).

tff(c_8888,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_323])).

tff(c_8894,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_96])).

tff(c_8893,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_90])).

tff(c_8890,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_215])).

tff(c_8881,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_8860,c_6041])).

tff(c_10721,plain,(
    ! [A_879] :
      ( v1_funct_2(k2_funct_1(A_879),k1_relat_1(k2_funct_1(A_879)),k1_relat_1(A_879))
      | ~ v1_funct_1(k2_funct_1(A_879))
      | ~ v1_relat_1(k2_funct_1(A_879))
      | ~ v2_funct_1(A_879)
      | ~ v1_funct_1(A_879)
      | ~ v1_relat_1(A_879) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6420,c_82])).

tff(c_10730,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8881,c_10721])).

tff(c_10742,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8888,c_8894,c_8893,c_8890,c_10730])).

tff(c_10743,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10742])).

tff(c_10746,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_10743])).

tff(c_10750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8888,c_8894,c_10746])).

tff(c_10752,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10742])).

tff(c_4787,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) = '#skF_5'
      | k2_relat_1(A_20) != '#skF_5'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_4780,c_26])).

tff(c_8863,plain,(
    ! [A_20] :
      ( k1_relat_1(A_20) = '#skF_4'
      | k2_relat_1(A_20) != '#skF_4'
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8860,c_8860,c_4787])).

tff(c_10759,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10752,c_8863])).

tff(c_10775,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10759])).

tff(c_10781,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10775])).

tff(c_10787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8888,c_8894,c_8893,c_8881,c_10781])).

tff(c_10788,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10759])).

tff(c_10813,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10788,c_80])).

tff(c_10838,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10752,c_8890,c_8878,c_10813])).

tff(c_10840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9106,c_10838])).

tff(c_10841,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_10842,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_11887,plain,(
    ! [A_976,B_977,C_978] :
      ( k1_relset_1(A_976,B_977,C_978) = k1_relat_1(C_978)
      | ~ m1_subset_1(C_978,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_11911,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10842,c_11887])).

tff(c_12268,plain,(
    ! [B_1012,C_1013,A_1014] :
      ( k1_xboole_0 = B_1012
      | v1_funct_2(C_1013,A_1014,B_1012)
      | k1_relset_1(A_1014,B_1012,C_1013) != A_1014
      | ~ m1_subset_1(C_1013,k1_zfmisc_1(k2_zfmisc_1(A_1014,B_1012))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12280,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10842,c_12268])).

tff(c_12305,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11911,c_12280])).

tff(c_12306,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_10841,c_12305])).

tff(c_12315,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12306])).

tff(c_12318,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12315])).

tff(c_12321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10878,c_96,c_90,c_12031,c_12318])).

tff(c_12322,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12306])).

tff(c_10886,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10878,c_28])).

tff(c_11080,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10886])).

tff(c_12352,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12322,c_11080])).

tff(c_10887,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10878,c_26])).

tff(c_11086,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_11080,c_10887])).

tff(c_12033,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12031,c_11086])).

tff(c_12333,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12322,c_12033])).

tff(c_11913,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_11887])).

tff(c_60,plain,(
    ! [B_36,A_35,C_37] :
      ( k1_xboole_0 = B_36
      | k1_relset_1(A_35,B_36,C_37) = A_35
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12429,plain,(
    ! [B_1018,A_1019,C_1020] :
      ( B_1018 = '#skF_3'
      | k1_relset_1(A_1019,B_1018,C_1020) = A_1019
      | ~ v1_funct_2(C_1020,A_1019,B_1018)
      | ~ m1_subset_1(C_1020,k1_zfmisc_1(k2_zfmisc_1(A_1019,B_1018))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12322,c_60])).

tff(c_12447,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_12429])).

tff(c_12462,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11913,c_12447])).

tff(c_12464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12352,c_12333,c_12462])).

tff(c_12465,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10886])).

tff(c_13535,plain,(
    ! [A_1122,B_1123,C_1124] :
      ( k2_relset_1(A_1122,B_1123,C_1124) = k2_relat_1(C_1124)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(A_1122,B_1123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13548,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_13535])).

tff(c_13563,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_12465,c_13548])).

tff(c_13598,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13563,c_6])).

tff(c_13593,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13563,c_13563,c_16])).

tff(c_10926,plain,(
    ! [B_888,A_889] :
      ( v1_xboole_0(B_888)
      | ~ m1_subset_1(B_888,k1_zfmisc_1(A_889))
      | ~ v1_xboole_0(A_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10958,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10842,c_10926])).

tff(c_13171,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10958])).

tff(c_13742,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13593,c_13171])).

tff(c_13745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13598,c_13742])).

tff(c_13747,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10958])).

tff(c_13778,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13747,c_8])).

tff(c_13796,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_13778,c_12])).

tff(c_13798,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13796])).

tff(c_13826,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13798,c_6])).

tff(c_13823,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13798,c_13798,c_14])).

tff(c_10963,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_92,c_10926])).

tff(c_10990,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10963])).

tff(c_13990,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13823,c_10990])).

tff(c_13994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13826,c_13990])).

tff(c_13995,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13796])).

tff(c_14024,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13995,c_6])).

tff(c_14019,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13995,c_13995,c_16])).

tff(c_14267,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14019,c_10990])).

tff(c_14271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14024,c_14267])).

tff(c_14273,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10963])).

tff(c_14272,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10963])).

tff(c_14277,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14272,c_8])).

tff(c_14359,plain,(
    ! [A_1168] :
      ( A_1168 = '#skF_5'
      | ~ v1_xboole_0(A_1168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_8])).

tff(c_14370,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14273,c_14359])).

tff(c_14744,plain,(
    ! [B_1200,A_1201] :
      ( B_1200 = '#skF_5'
      | A_1201 = '#skF_5'
      | k2_zfmisc_1(A_1201,B_1200) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_14277,c_14277,c_12])).

tff(c_14754,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_14370,c_14744])).

tff(c_14759,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14754])).

tff(c_14814,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14759,c_14272])).

tff(c_14290,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_14277,c_14])).

tff(c_14807,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14759,c_14759,c_14290])).

tff(c_14550,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10958])).

tff(c_15054,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14807,c_14550])).

tff(c_15057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14814,c_15054])).

tff(c_15058,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14754])).

tff(c_15087,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15058,c_14272])).

tff(c_14288,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_14277,c_16])).

tff(c_15082,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15058,c_15058,c_14288])).

tff(c_15175,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15082,c_14550])).

tff(c_15178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15087,c_15175])).

tff(c_15179,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10958])).

tff(c_14291,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14277,c_8])).

tff(c_15184,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15179,c_14291])).

tff(c_15200,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15184,c_10841])).

tff(c_15180,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10958])).

tff(c_15233,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15180,c_14291])).

tff(c_15244,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15233,c_76])).

tff(c_15343,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_3'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_15244,c_22])).

tff(c_15349,plain,(
    v1_xboole_0('#skF_2'('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14272,c_15343])).

tff(c_15353,plain,(
    '#skF_2'('#skF_4','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_15349,c_14291])).

tff(c_15390,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15353,c_66])).

tff(c_15405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15200,c_15390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.33  
% 9.33/3.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 9.33/3.33  
% 9.33/3.33  %Foreground sorts:
% 9.33/3.33  
% 9.33/3.33  
% 9.33/3.33  %Background operators:
% 9.33/3.33  
% 9.33/3.33  
% 9.33/3.33  %Foreground operators:
% 9.33/3.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.33/3.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.33/3.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.33/3.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.33/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.33/3.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.33/3.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/3.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.33/3.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.33/3.33  tff('#skF_5', type, '#skF_5': $i).
% 9.33/3.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.33/3.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.33/3.33  tff('#skF_3', type, '#skF_3': $i).
% 9.33/3.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.33/3.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.33/3.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.33/3.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.33/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.33/3.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.33/3.33  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.33/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.33/3.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.33/3.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.33/3.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.33/3.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.33/3.33  
% 9.33/3.36  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.33/3.36  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.33/3.36  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.33/3.36  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.33/3.36  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.33/3.36  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 9.33/3.36  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.33/3.36  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.33/3.36  tff(f_158, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.33/3.36  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.33/3.36  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.33/3.36  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.33/3.36  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.33/3.36  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.33/3.36  tff(f_146, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.33/3.36  tff(c_88, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_10852, plain, (![C_884, A_885, B_886]: (v1_relat_1(C_884) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_885, B_886))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.33/3.36  tff(c_10878, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_10852])).
% 9.33/3.36  tff(c_96, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_90, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_12004, plain, (![A_991, B_992, C_993]: (k2_relset_1(A_991, B_992, C_993)=k2_relat_1(C_993) | ~m1_subset_1(C_993, k1_zfmisc_1(k2_zfmisc_1(A_991, B_992))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_12016, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_12004])).
% 9.33/3.36  tff(c_12031, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_12016])).
% 9.33/3.36  tff(c_40, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.33/3.36  tff(c_30, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.33/3.36  tff(c_86, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_185, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 9.33/3.36  tff(c_188, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_185])).
% 9.33/3.36  tff(c_191, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_188])).
% 9.33/3.36  tff(c_193, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.33/3.36  tff(c_199, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_193])).
% 9.33/3.36  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_199])).
% 9.33/3.36  tff(c_214, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_86])).
% 9.33/3.36  tff(c_254, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_214])).
% 9.33/3.36  tff(c_306, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.33/3.36  tff(c_323, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_306])).
% 9.33/3.36  tff(c_1559, plain, (![A_217, B_218, C_219]: (k2_relset_1(A_217, B_218, C_219)=k2_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_1571, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_1559])).
% 9.33/3.36  tff(c_1586, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1571])).
% 9.33/3.36  tff(c_26, plain, (![A_20]: (k1_relat_1(A_20)=k1_xboole_0 | k2_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.33/3.36  tff(c_333, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_323, c_26])).
% 9.33/3.36  tff(c_342, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_333])).
% 9.33/3.36  tff(c_1589, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_342])).
% 9.33/3.36  tff(c_94, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 9.33/3.36  tff(c_1399, plain, (![A_202, B_203, C_204]: (k1_relset_1(A_202, B_203, C_204)=k1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.33/3.36  tff(c_1421, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_1399])).
% 9.33/3.36  tff(c_1783, plain, (![B_239, A_240, C_241]: (k1_xboole_0=B_239 | k1_relset_1(A_240, B_239, C_241)=A_240 | ~v1_funct_2(C_241, A_240, B_239) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.33/3.36  tff(c_1798, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_1783])).
% 9.33/3.36  tff(c_1821, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1421, c_1798])).
% 9.33/3.36  tff(c_1822, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1589, c_1821])).
% 9.33/3.36  tff(c_38, plain, (![A_23]: (k2_relat_1(k2_funct_1(A_23))=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.33/3.36  tff(c_32, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.33/3.36  tff(c_215, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_86])).
% 9.33/3.36  tff(c_1353, plain, (![A_198]: (k2_relat_1(k2_funct_1(A_198))=k1_relat_1(A_198) | ~v2_funct_1(A_198) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.33/3.36  tff(c_82, plain, (![A_43]: (v1_funct_2(A_43, k1_relat_1(A_43), k2_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.33/3.36  tff(c_2987, plain, (![A_304]: (v1_funct_2(k2_funct_1(A_304), k1_relat_1(k2_funct_1(A_304)), k1_relat_1(A_304)) | ~v1_funct_1(k2_funct_1(A_304)) | ~v1_relat_1(k2_funct_1(A_304)) | ~v2_funct_1(A_304) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_82])).
% 9.33/3.36  tff(c_2996, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1822, c_2987])).
% 9.33/3.36  tff(c_3011, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_96, c_90, c_215, c_2996])).
% 9.33/3.36  tff(c_3014, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3011])).
% 9.33/3.36  tff(c_3017, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_3014])).
% 9.33/3.36  tff(c_3021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_96, c_3017])).
% 9.33/3.36  tff(c_3023, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3011])).
% 9.33/3.36  tff(c_1477, plain, (![A_214]: (m1_subset_1(A_214, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_214), k2_relat_1(A_214)))) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.33/3.36  tff(c_3407, plain, (![A_340]: (m1_subset_1(k2_funct_1(A_340), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_340), k2_relat_1(k2_funct_1(A_340))))) | ~v1_funct_1(k2_funct_1(A_340)) | ~v1_relat_1(k2_funct_1(A_340)) | ~v2_funct_1(A_340) | ~v1_funct_1(A_340) | ~v1_relat_1(A_340))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1477])).
% 9.33/3.36  tff(c_3441, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1586, c_3407])).
% 9.33/3.36  tff(c_3470, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_96, c_90, c_3023, c_215, c_3441])).
% 9.33/3.36  tff(c_3504, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38, c_3470])).
% 9.33/3.36  tff(c_3522, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_96, c_90, c_1822, c_3504])).
% 9.33/3.36  tff(c_3524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_3522])).
% 9.33/3.36  tff(c_3526, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_333])).
% 9.33/3.36  tff(c_4553, plain, (![A_442, B_443, C_444]: (k2_relset_1(A_442, B_443, C_444)=k2_relat_1(C_444) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_4566, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_4553])).
% 9.33/3.36  tff(c_4581, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3526, c_4566])).
% 9.33/3.36  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.33/3.36  tff(c_4614, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_6])).
% 9.33/3.36  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.33/3.36  tff(c_4611, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4581, c_4581, c_14])).
% 9.33/3.36  tff(c_255, plain, (![B_80, A_81]: (v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.33/3.36  tff(c_272, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_255])).
% 9.33/3.36  tff(c_334, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_272])).
% 9.33/3.36  tff(c_4770, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4611, c_334])).
% 9.33/3.36  tff(c_4774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4614, c_4770])).
% 9.33/3.36  tff(c_4776, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_272])).
% 9.33/3.36  tff(c_4775, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_272])).
% 9.33/3.36  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.33/3.36  tff(c_4780, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4775, c_8])).
% 9.33/3.36  tff(c_6050, plain, (![A_554]: (A_554='#skF_5' | ~v1_xboole_0(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_8])).
% 9.33/3.36  tff(c_6057, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_4776, c_6050])).
% 9.33/3.36  tff(c_12, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.33/3.36  tff(c_6470, plain, (![B_588, A_589]: (B_588='#skF_5' | A_589='#skF_5' | k2_zfmisc_1(A_589, B_588)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_4780, c_12])).
% 9.33/3.36  tff(c_6480, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6057, c_6470])).
% 9.33/3.36  tff(c_6485, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_6480])).
% 9.33/3.36  tff(c_4838, plain, (![A_458]: (A_458='#skF_5' | ~v1_xboole_0(A_458))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_8])).
% 9.33/3.36  tff(c_4845, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_4776, c_4838])).
% 9.33/3.36  tff(c_5202, plain, (![B_490, A_491]: (B_490='#skF_5' | A_491='#skF_5' | k2_zfmisc_1(A_491, B_490)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_4780, c_12])).
% 9.33/3.36  tff(c_5212, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4845, c_5202])).
% 9.33/3.36  tff(c_5217, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_5212])).
% 9.33/3.36  tff(c_28, plain, (![A_20]: (k2_relat_1(A_20)=k1_xboole_0 | k1_relat_1(A_20)!=k1_xboole_0 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.33/3.36  tff(c_332, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_323, c_28])).
% 9.33/3.36  tff(c_4836, plain, (k2_relat_1('#skF_5')='#skF_5' | k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_332])).
% 9.33/3.36  tff(c_4837, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(splitLeft, [status(thm)], [c_4836])).
% 9.33/3.36  tff(c_5236, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5217, c_5217, c_4837])).
% 9.33/3.36  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.33/3.36  tff(c_4790, plain, (![A_13]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_20])).
% 9.33/3.36  tff(c_5233, plain, (![A_13]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_5217, c_4790])).
% 9.33/3.36  tff(c_5369, plain, (![A_501, B_502, C_503]: (k1_relset_1(A_501, B_502, C_503)=k1_relat_1(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_501, B_502))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.33/3.36  tff(c_5622, plain, (![A_523, B_524]: (k1_relset_1(A_523, B_524, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5233, c_5369])).
% 9.33/3.36  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.33/3.36  tff(c_4848, plain, (![B_459]: (k2_zfmisc_1('#skF_5', B_459)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_16])).
% 9.33/3.36  tff(c_76, plain, (![A_39, B_40]: (m1_subset_1('#skF_2'(A_39, B_40), k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.33/3.36  tff(c_5036, plain, (![B_476]: (m1_subset_1('#skF_2'('#skF_5', B_476), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4848, c_76])).
% 9.33/3.36  tff(c_22, plain, (![B_16, A_14]: (v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.33/3.36  tff(c_5044, plain, (![B_476]: (v1_xboole_0('#skF_2'('#skF_5', B_476)) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_5036, c_22])).
% 9.33/3.36  tff(c_5055, plain, (![B_477]: (v1_xboole_0('#skF_2'('#skF_5', B_477)))), inference(demodulation, [status(thm), theory('equality')], [c_4775, c_5044])).
% 9.33/3.36  tff(c_4792, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_8])).
% 9.33/3.36  tff(c_5062, plain, (![B_477]: ('#skF_2'('#skF_5', B_477)='#skF_5')), inference(resolution, [status(thm)], [c_5055, c_4792])).
% 9.33/3.36  tff(c_5224, plain, (![B_477]: ('#skF_2'('#skF_3', B_477)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5217, c_5217, c_5062])).
% 9.33/3.36  tff(c_66, plain, (![A_39, B_40]: (v1_funct_2('#skF_2'(A_39, B_40), A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.33/3.36  tff(c_5240, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5217, c_4780])).
% 9.33/3.36  tff(c_58, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.33/3.36  tff(c_102, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 9.33/3.36  tff(c_5566, plain, (![B_517, C_518]: (k1_relset_1('#skF_3', B_517, C_518)='#skF_3' | ~v1_funct_2(C_518, '#skF_3', B_517) | ~m1_subset_1(C_518, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5240, c_5240, c_5240, c_5240, c_102])).
% 9.33/3.36  tff(c_5574, plain, (![B_40]: (k1_relset_1('#skF_3', B_40, '#skF_2'('#skF_3', B_40))='#skF_3' | ~m1_subset_1('#skF_2'('#skF_3', B_40), k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_5566])).
% 9.33/3.36  tff(c_5583, plain, (![B_40]: (k1_relset_1('#skF_3', B_40, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5233, c_5224, c_5224, c_5574])).
% 9.33/3.36  tff(c_5627, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5622, c_5583])).
% 9.33/3.36  tff(c_5634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5236, c_5627])).
% 9.33/3.36  tff(c_5635, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5212])).
% 9.33/3.36  tff(c_4924, plain, (k1_relat_1('#skF_5')='#skF_5' | k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_333])).
% 9.33/3.36  tff(c_4925, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4837, c_4924])).
% 9.33/3.36  tff(c_5648, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5635, c_5635, c_4925])).
% 9.33/3.36  tff(c_5734, plain, (![A_534]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_534)))), inference(demodulation, [status(thm), theory('equality')], [c_5635, c_4790])).
% 9.33/3.36  tff(c_48, plain, (![A_32, B_33, C_34]: (k2_relset_1(A_32, B_33, C_34)=k2_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_6028, plain, (![A_552, B_553]: (k2_relset_1(A_552, B_553, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5734, c_48])).
% 9.33/3.36  tff(c_5664, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5635, c_88])).
% 9.33/3.36  tff(c_6032, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6028, c_5664])).
% 9.33/3.36  tff(c_6039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5648, c_6032])).
% 9.33/3.36  tff(c_6040, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4836])).
% 9.33/3.36  tff(c_6506, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_6485, c_6040])).
% 9.33/3.36  tff(c_6503, plain, (![A_13]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_4790])).
% 9.33/3.36  tff(c_6826, plain, (![A_607, B_608, C_609]: (k2_relset_1(A_607, B_608, C_609)=k2_relat_1(C_609) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_6836, plain, (![A_607, B_608]: (k2_relset_1(A_607, B_608, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6503, c_6826])).
% 9.33/3.36  tff(c_6862, plain, (![A_612, B_613]: (k2_relset_1(A_612, B_613, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6506, c_6836])).
% 9.33/3.36  tff(c_6515, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_88])).
% 9.33/3.36  tff(c_6866, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6862, c_6515])).
% 9.33/3.36  tff(c_4791, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_14])).
% 9.33/3.36  tff(c_6501, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_6485, c_4791])).
% 9.33/3.36  tff(c_6513, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_254])).
% 9.33/3.36  tff(c_6800, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6501, c_6513])).
% 9.33/3.36  tff(c_6877, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6866, c_6800])).
% 9.33/3.36  tff(c_6512, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_323])).
% 9.33/3.36  tff(c_6898, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6512])).
% 9.33/3.36  tff(c_6518, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_96])).
% 9.33/3.36  tff(c_6896, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6518])).
% 9.33/3.36  tff(c_6517, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_90])).
% 9.33/3.36  tff(c_6897, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6517])).
% 9.33/3.36  tff(c_6514, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_215])).
% 9.33/3.36  tff(c_6893, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6514])).
% 9.33/3.36  tff(c_6041, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_4836])).
% 9.33/3.36  tff(c_6505, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_6485, c_6041])).
% 9.33/3.36  tff(c_6891, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6866, c_6505])).
% 9.33/3.36  tff(c_6420, plain, (![A_585]: (k2_relat_1(k2_funct_1(A_585))=k1_relat_1(A_585) | ~v2_funct_1(A_585) | ~v1_funct_1(A_585) | ~v1_relat_1(A_585))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.33/3.36  tff(c_8743, plain, (![A_744]: (v1_funct_2(k2_funct_1(A_744), k1_relat_1(k2_funct_1(A_744)), k1_relat_1(A_744)) | ~v1_funct_1(k2_funct_1(A_744)) | ~v1_relat_1(k2_funct_1(A_744)) | ~v2_funct_1(A_744) | ~v1_funct_1(A_744) | ~v1_relat_1(A_744))), inference(superposition, [status(thm), theory('equality')], [c_6420, c_82])).
% 9.33/3.36  tff(c_8752, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6891, c_8743])).
% 9.33/3.36  tff(c_8764, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6898, c_6896, c_6897, c_6893, c_8752])).
% 9.33/3.36  tff(c_8765, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8764])).
% 9.33/3.36  tff(c_8768, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_8765])).
% 9.33/3.36  tff(c_8772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6898, c_6896, c_8768])).
% 9.33/3.36  tff(c_8774, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8764])).
% 9.33/3.36  tff(c_6880, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6866, c_6501])).
% 9.33/3.36  tff(c_6889, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6866, c_6506])).
% 9.33/3.36  tff(c_4785, plain, (![A_20]: (k2_relat_1(A_20)='#skF_5' | k1_relat_1(A_20)!='#skF_5' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_28])).
% 9.33/3.36  tff(c_6488, plain, (![A_20]: (k2_relat_1(A_20)='#skF_3' | k1_relat_1(A_20)!='#skF_3' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_6485, c_4785])).
% 9.33/3.36  tff(c_7303, plain, (![A_20]: (k2_relat_1(A_20)='#skF_4' | k1_relat_1(A_20)!='#skF_4' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_6866, c_6866, c_6488])).
% 9.33/3.36  tff(c_8782, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_8774, c_7303])).
% 9.33/3.36  tff(c_8797, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8782])).
% 9.33/3.36  tff(c_8800, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_8797])).
% 9.33/3.36  tff(c_8803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6898, c_6896, c_6897, c_6889, c_8800])).
% 9.33/3.36  tff(c_8804, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_8782])).
% 9.33/3.36  tff(c_80, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.33/3.36  tff(c_8827, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8804, c_80])).
% 9.33/3.36  tff(c_8857, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8774, c_6893, c_6880, c_8827])).
% 9.33/3.36  tff(c_8859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6877, c_8857])).
% 9.33/3.36  tff(c_8860, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_6480])).
% 9.33/3.36  tff(c_4789, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_16])).
% 9.33/3.36  tff(c_8878, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_8860, c_4789])).
% 9.33/3.36  tff(c_8889, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_254])).
% 9.33/3.36  tff(c_9106, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8878, c_8889])).
% 9.33/3.36  tff(c_8888, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_323])).
% 9.33/3.36  tff(c_8894, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_96])).
% 9.33/3.36  tff(c_8893, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_90])).
% 9.33/3.36  tff(c_8890, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_215])).
% 9.33/3.36  tff(c_8881, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_8860, c_6041])).
% 9.33/3.36  tff(c_10721, plain, (![A_879]: (v1_funct_2(k2_funct_1(A_879), k1_relat_1(k2_funct_1(A_879)), k1_relat_1(A_879)) | ~v1_funct_1(k2_funct_1(A_879)) | ~v1_relat_1(k2_funct_1(A_879)) | ~v2_funct_1(A_879) | ~v1_funct_1(A_879) | ~v1_relat_1(A_879))), inference(superposition, [status(thm), theory('equality')], [c_6420, c_82])).
% 9.33/3.36  tff(c_10730, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8881, c_10721])).
% 9.33/3.36  tff(c_10742, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8888, c_8894, c_8893, c_8890, c_10730])).
% 9.33/3.36  tff(c_10743, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10742])).
% 9.33/3.36  tff(c_10746, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_10743])).
% 9.33/3.36  tff(c_10750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8888, c_8894, c_10746])).
% 9.33/3.36  tff(c_10752, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10742])).
% 9.33/3.36  tff(c_4787, plain, (![A_20]: (k1_relat_1(A_20)='#skF_5' | k2_relat_1(A_20)!='#skF_5' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_4780, c_26])).
% 9.33/3.36  tff(c_8863, plain, (![A_20]: (k1_relat_1(A_20)='#skF_4' | k2_relat_1(A_20)!='#skF_4' | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_8860, c_8860, c_4787])).
% 9.33/3.36  tff(c_10759, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4' | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_10752, c_8863])).
% 9.33/3.36  tff(c_10775, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_10759])).
% 9.33/3.36  tff(c_10781, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_10775])).
% 9.33/3.36  tff(c_10787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8888, c_8894, c_8893, c_8881, c_10781])).
% 9.33/3.36  tff(c_10788, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_10759])).
% 9.33/3.36  tff(c_10813, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10788, c_80])).
% 9.33/3.36  tff(c_10838, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10752, c_8890, c_8878, c_10813])).
% 9.33/3.36  tff(c_10840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9106, c_10838])).
% 9.33/3.36  tff(c_10841, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_214])).
% 9.33/3.36  tff(c_10842, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_214])).
% 9.33/3.36  tff(c_11887, plain, (![A_976, B_977, C_978]: (k1_relset_1(A_976, B_977, C_978)=k1_relat_1(C_978) | ~m1_subset_1(C_978, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.33/3.36  tff(c_11911, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_10842, c_11887])).
% 9.33/3.36  tff(c_12268, plain, (![B_1012, C_1013, A_1014]: (k1_xboole_0=B_1012 | v1_funct_2(C_1013, A_1014, B_1012) | k1_relset_1(A_1014, B_1012, C_1013)!=A_1014 | ~m1_subset_1(C_1013, k1_zfmisc_1(k2_zfmisc_1(A_1014, B_1012))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.33/3.36  tff(c_12280, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_10842, c_12268])).
% 9.33/3.36  tff(c_12305, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11911, c_12280])).
% 9.33/3.36  tff(c_12306, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_10841, c_12305])).
% 9.33/3.36  tff(c_12315, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_12306])).
% 9.33/3.36  tff(c_12318, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_12315])).
% 9.33/3.36  tff(c_12321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10878, c_96, c_90, c_12031, c_12318])).
% 9.33/3.36  tff(c_12322, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_12306])).
% 9.33/3.36  tff(c_10886, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10878, c_28])).
% 9.33/3.36  tff(c_11080, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10886])).
% 9.33/3.36  tff(c_12352, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12322, c_11080])).
% 9.33/3.36  tff(c_10887, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10878, c_26])).
% 9.33/3.36  tff(c_11086, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_11080, c_10887])).
% 9.33/3.36  tff(c_12033, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12031, c_11086])).
% 9.33/3.36  tff(c_12333, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12322, c_12033])).
% 9.33/3.36  tff(c_11913, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_11887])).
% 9.33/3.36  tff(c_60, plain, (![B_36, A_35, C_37]: (k1_xboole_0=B_36 | k1_relset_1(A_35, B_36, C_37)=A_35 | ~v1_funct_2(C_37, A_35, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.33/3.36  tff(c_12429, plain, (![B_1018, A_1019, C_1020]: (B_1018='#skF_3' | k1_relset_1(A_1019, B_1018, C_1020)=A_1019 | ~v1_funct_2(C_1020, A_1019, B_1018) | ~m1_subset_1(C_1020, k1_zfmisc_1(k2_zfmisc_1(A_1019, B_1018))))), inference(demodulation, [status(thm), theory('equality')], [c_12322, c_60])).
% 9.33/3.36  tff(c_12447, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_92, c_12429])).
% 9.33/3.36  tff(c_12462, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11913, c_12447])).
% 9.33/3.36  tff(c_12464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12352, c_12333, c_12462])).
% 9.33/3.36  tff(c_12465, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10886])).
% 9.33/3.36  tff(c_13535, plain, (![A_1122, B_1123, C_1124]: (k2_relset_1(A_1122, B_1123, C_1124)=k2_relat_1(C_1124) | ~m1_subset_1(C_1124, k1_zfmisc_1(k2_zfmisc_1(A_1122, B_1123))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.33/3.36  tff(c_13548, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_13535])).
% 9.33/3.36  tff(c_13563, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_12465, c_13548])).
% 9.33/3.36  tff(c_13598, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13563, c_6])).
% 9.33/3.36  tff(c_13593, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13563, c_13563, c_16])).
% 9.33/3.36  tff(c_10926, plain, (![B_888, A_889]: (v1_xboole_0(B_888) | ~m1_subset_1(B_888, k1_zfmisc_1(A_889)) | ~v1_xboole_0(A_889))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.33/3.36  tff(c_10958, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10842, c_10926])).
% 9.33/3.36  tff(c_13171, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_10958])).
% 9.33/3.36  tff(c_13742, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13593, c_13171])).
% 9.33/3.36  tff(c_13745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13598, c_13742])).
% 9.33/3.36  tff(c_13747, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_10958])).
% 9.33/3.36  tff(c_13778, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_13747, c_8])).
% 9.33/3.36  tff(c_13796, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_13778, c_12])).
% 9.33/3.36  tff(c_13798, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13796])).
% 9.33/3.36  tff(c_13826, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13798, c_6])).
% 9.33/3.36  tff(c_13823, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13798, c_13798, c_14])).
% 9.33/3.36  tff(c_10963, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_10926])).
% 9.33/3.36  tff(c_10990, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_10963])).
% 9.33/3.36  tff(c_13990, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13823, c_10990])).
% 9.33/3.36  tff(c_13994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13826, c_13990])).
% 9.33/3.36  tff(c_13995, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_13796])).
% 9.33/3.36  tff(c_14024, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13995, c_6])).
% 9.33/3.36  tff(c_14019, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13995, c_13995, c_16])).
% 9.33/3.36  tff(c_14267, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14019, c_10990])).
% 9.33/3.36  tff(c_14271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14024, c_14267])).
% 9.33/3.36  tff(c_14273, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_10963])).
% 9.33/3.36  tff(c_14272, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_10963])).
% 9.33/3.36  tff(c_14277, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14272, c_8])).
% 9.33/3.36  tff(c_14359, plain, (![A_1168]: (A_1168='#skF_5' | ~v1_xboole_0(A_1168))), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_8])).
% 9.33/3.36  tff(c_14370, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_14273, c_14359])).
% 9.33/3.36  tff(c_14744, plain, (![B_1200, A_1201]: (B_1200='#skF_5' | A_1201='#skF_5' | k2_zfmisc_1(A_1201, B_1200)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_14277, c_14277, c_12])).
% 9.33/3.36  tff(c_14754, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_14370, c_14744])).
% 9.33/3.36  tff(c_14759, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_14754])).
% 9.33/3.36  tff(c_14814, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14759, c_14272])).
% 9.33/3.36  tff(c_14290, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_14277, c_14])).
% 9.33/3.36  tff(c_14807, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14759, c_14759, c_14290])).
% 9.33/3.36  tff(c_14550, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_10958])).
% 9.33/3.36  tff(c_15054, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14807, c_14550])).
% 9.33/3.36  tff(c_15057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14814, c_15054])).
% 9.33/3.36  tff(c_15058, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_14754])).
% 9.33/3.36  tff(c_15087, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15058, c_14272])).
% 9.33/3.36  tff(c_14288, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_14277, c_16])).
% 9.33/3.36  tff(c_15082, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15058, c_15058, c_14288])).
% 9.33/3.36  tff(c_15175, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15082, c_14550])).
% 9.33/3.36  tff(c_15178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15087, c_15175])).
% 9.33/3.36  tff(c_15179, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_10958])).
% 9.33/3.36  tff(c_14291, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_14277, c_8])).
% 9.33/3.36  tff(c_15184, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_15179, c_14291])).
% 9.33/3.36  tff(c_15200, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15184, c_10841])).
% 9.33/3.36  tff(c_15180, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_10958])).
% 9.33/3.36  tff(c_15233, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_15180, c_14291])).
% 9.33/3.36  tff(c_15244, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15233, c_76])).
% 9.33/3.36  tff(c_15343, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_3')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_15244, c_22])).
% 9.33/3.36  tff(c_15349, plain, (v1_xboole_0('#skF_2'('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14272, c_15343])).
% 9.33/3.36  tff(c_15353, plain, ('#skF_2'('#skF_4', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_15349, c_14291])).
% 9.33/3.36  tff(c_15390, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15353, c_66])).
% 9.33/3.36  tff(c_15405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15200, c_15390])).
% 9.33/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.33/3.36  
% 9.33/3.36  Inference rules
% 9.33/3.36  ----------------------
% 9.33/3.36  #Ref     : 0
% 9.33/3.36  #Sup     : 3345
% 9.33/3.36  #Fact    : 0
% 9.33/3.36  #Define  : 0
% 9.33/3.36  #Split   : 41
% 9.33/3.36  #Chain   : 0
% 9.33/3.36  #Close   : 0
% 9.33/3.36  
% 9.33/3.36  Ordering : KBO
% 9.33/3.36  
% 9.33/3.36  Simplification rules
% 9.33/3.36  ----------------------
% 9.33/3.36  #Subsume      : 395
% 9.33/3.36  #Demod        : 4397
% 9.33/3.36  #Tautology    : 1961
% 9.33/3.36  #SimpNegUnit  : 72
% 9.33/3.36  #BackRed      : 635
% 9.33/3.36  
% 9.33/3.36  #Partial instantiations: 0
% 9.33/3.36  #Strategies tried      : 1
% 9.33/3.37  
% 9.33/3.37  Timing (in seconds)
% 9.33/3.37  ----------------------
% 9.33/3.37  Preprocessing        : 0.35
% 9.33/3.37  Parsing              : 0.18
% 9.33/3.37  CNF conversion       : 0.02
% 9.33/3.37  Main loop            : 2.19
% 9.33/3.37  Inferencing          : 0.76
% 9.33/3.37  Reduction            : 0.80
% 9.33/3.37  Demodulation         : 0.58
% 9.33/3.37  BG Simplification    : 0.07
% 9.33/3.37  Subsumption          : 0.36
% 9.33/3.37  Abstraction          : 0.09
% 9.33/3.37  MUC search           : 0.00
% 9.33/3.37  Cooper               : 0.00
% 9.33/3.37  Total                : 2.63
% 9.33/3.37  Index Insertion      : 0.00
% 9.33/3.37  Index Deletion       : 0.00
% 9.33/3.37  Index Matching       : 0.00
% 9.33/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
