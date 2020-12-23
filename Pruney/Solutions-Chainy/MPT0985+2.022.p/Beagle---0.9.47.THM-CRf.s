%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  260 (5489 expanded)
%              Number of leaves         :   37 (1750 expanded)
%              Depth                    :   17
%              Number of atoms          :  488 (13904 expanded)
%              Number of equality atoms :  117 (3067 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1898,plain,(
    ! [C_177,A_178,B_179] :
      ( v1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1915,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1898])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2028,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_relset_1(A_191,B_192,C_193) = k2_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2038,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2028])).

tff(c_2048,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2038])).

tff(c_32,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [A_41] :
      ( v1_funct_1(k2_funct_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_144,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_140])).

tff(c_147,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_144])).

tff(c_148,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_148])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_155])).

tff(c_165,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_178,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_182,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_193,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_206,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_193])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_357,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_372,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_357])).

tff(c_705,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_721,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_705])).

tff(c_736,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_372,c_721])).

tff(c_738,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_30,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_591,plain,(
    ! [B_97,A_98] :
      ( m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97),A_98)))
      | ~ r1_tarski(k2_relat_1(B_97),A_98)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1131,plain,(
    ! [B_135,A_136] :
      ( v1_xboole_0(B_135)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_135),A_136))
      | ~ r1_tarski(k2_relat_1(B_135),A_136)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_591,c_14])).

tff(c_1141,plain,(
    ! [B_135] :
      ( v1_xboole_0(B_135)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(B_135),k1_xboole_0)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1131])).

tff(c_1170,plain,(
    ! [B_139] :
      ( v1_xboole_0(B_139)
      | ~ r1_tarski(k2_relat_1(B_139),k1_xboole_0)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1141])).

tff(c_1360,plain,(
    ! [A_155] :
      ( v1_xboole_0(k2_funct_1(A_155))
      | ~ r1_tarski(k1_relat_1(A_155),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_155))
      | ~ v1_relat_1(k2_funct_1(A_155))
      | ~ v2_funct_1(A_155)
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1170])).

tff(c_1363,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_1360])).

tff(c_1371,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_74,c_68,c_166,c_1363])).

tff(c_1374,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1371])).

tff(c_1377,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1374])).

tff(c_1381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_74,c_1377])).

tff(c_1383,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_322,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_329,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_322])).

tff(c_338,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_329])).

tff(c_390,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_639,plain,(
    ! [A_103] :
      ( r1_tarski(A_103,k2_zfmisc_1(k1_relat_1(A_103),k2_relat_1(A_103)))
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_390,c_16])).

tff(c_1453,plain,(
    ! [A_159] :
      ( r1_tarski(k2_funct_1(A_159),k2_zfmisc_1(k2_relat_1(A_159),k2_relat_1(k2_funct_1(A_159))))
      | ~ v1_funct_1(k2_funct_1(A_159))
      | ~ v1_relat_1(k2_funct_1(A_159))
      | ~ v2_funct_1(A_159)
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_639])).

tff(c_1474,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_1453])).

tff(c_1491,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_74,c_68,c_1383,c_166,c_1474])).

tff(c_1514,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1491])).

tff(c_1526,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_74,c_68,c_738,c_1514])).

tff(c_1528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1526])).

tff(c_1529,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_1560,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_2])).

tff(c_1556,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_1529,c_10])).

tff(c_408,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_390])).

tff(c_427,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_74,c_408])).

tff(c_452,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_427,c_14])).

tff(c_471,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_452])).

tff(c_1672,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1556,c_471])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1672])).

tff(c_1681,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_452])).

tff(c_119,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_1691,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1681,c_122])).

tff(c_1709,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1691,c_10])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1710,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_1691,c_20])).

tff(c_1721,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1710,c_338])).

tff(c_168,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_168])).

tff(c_177,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_1744,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_177])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1709,c_1744])).

tff(c_1862,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_1863,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_2141,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2166,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1863,c_2141])).

tff(c_2453,plain,(
    ! [B_236,C_237,A_238] :
      ( k1_xboole_0 = B_236
      | v1_funct_2(C_237,A_238,B_236)
      | k1_relset_1(A_238,B_236,C_237) != A_238
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2465,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1863,c_2453])).

tff(c_2485,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2166,c_2465])).

tff(c_2486,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1862,c_2485])).

tff(c_2491,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2486])).

tff(c_2494,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2491])).

tff(c_2497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_74,c_68,c_2048,c_2494])).

tff(c_2498,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_2527,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2522,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_2498,c_12])).

tff(c_2669,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_177])).

tff(c_2674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2527,c_2669])).

tff(c_2675,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_2685,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2675,c_122])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2708,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_22])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2709,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_4])).

tff(c_5288,plain,(
    ! [A_486,B_487,C_488] :
      ( k1_relset_1(A_486,B_487,C_488) = k1_relat_1(C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5352,plain,(
    ! [A_499,B_500,A_501] :
      ( k1_relset_1(A_499,B_500,A_501) = k1_relat_1(A_501)
      | ~ r1_tarski(A_501,k2_zfmisc_1(A_499,B_500)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5288])).

tff(c_5362,plain,(
    ! [A_499,B_500] : k1_relset_1(A_499,B_500,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2709,c_5352])).

tff(c_5364,plain,(
    ! [A_499,B_500] : k1_relset_1(A_499,B_500,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2708,c_5362])).

tff(c_2676,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4748,plain,(
    ! [A_455] :
      ( A_455 = '#skF_3'
      | ~ v1_xboole_0(A_455) ) ),
    inference(resolution,[status(thm)],[c_2675,c_6])).

tff(c_4755,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2676,c_4748])).

tff(c_4789,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4755,c_70])).

tff(c_44,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_5490,plain,(
    ! [C_521,B_522] :
      ( v1_funct_2(C_521,'#skF_3',B_522)
      | k1_relset_1('#skF_3',B_522,C_521) != '#skF_3'
      | ~ m1_subset_1(C_521,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_2685,c_2685,c_76])).

tff(c_5492,plain,(
    ! [B_522] :
      ( v1_funct_2('#skF_3','#skF_3',B_522)
      | k1_relset_1('#skF_3',B_522,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_4789,c_5490])).

tff(c_5498,plain,(
    ! [B_522] : v1_funct_2('#skF_3','#skF_3',B_522) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5364,c_5492])).

tff(c_2705,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_12])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4810,plain,(
    ! [B_457,A_458] :
      ( B_457 = '#skF_3'
      | A_458 = '#skF_3'
      | k2_zfmisc_1(A_458,B_457) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_2685,c_8])).

tff(c_4820,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4755,c_4810])).

tff(c_4825,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4820])).

tff(c_2689,plain,(
    ! [C_242,A_243,B_244] :
      ( v1_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2702,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2689])).

tff(c_4839,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_2702])).

tff(c_4845,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_74])).

tff(c_2707,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_20])).

tff(c_4837,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4825,c_2707])).

tff(c_4836,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4825,c_2708])).

tff(c_4963,plain,(
    ! [A_466] :
      ( v1_funct_2(A_466,k1_relat_1(A_466),k2_relat_1(A_466))
      | ~ v1_funct_1(A_466)
      | ~ v1_relat_1(A_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4966,plain,
    ( v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4836,c_4963])).

tff(c_4971,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4839,c_4845,c_4837,c_4966])).

tff(c_4827,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4825,c_4789])).

tff(c_4838,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_2685])).

tff(c_40,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_77,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_4867,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_1',A_23,'#skF_1')
      | A_23 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4838,c_4838,c_4838,c_4838,c_4838,c_77])).

tff(c_4868,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4867])).

tff(c_4929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4827,c_4868])).

tff(c_5099,plain,(
    ! [A_472] :
      ( v1_funct_2('#skF_1',A_472,'#skF_1')
      | A_472 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_4867])).

tff(c_4840,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_2675])).

tff(c_2706,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_10])).

tff(c_4829,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4825,c_2706])).

tff(c_2765,plain,(
    ! [A_248] :
      ( A_248 = '#skF_3'
      | ~ v1_xboole_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_122])).

tff(c_2772,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2676,c_2765])).

tff(c_2777,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2772,c_70])).

tff(c_4343,plain,(
    ! [B_418,A_419] :
      ( m1_subset_1(B_418,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_418),A_419)))
      | ~ r1_tarski(k2_relat_1(B_418),A_419)
      | ~ v1_funct_1(B_418)
      | ~ v1_relat_1(B_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4460,plain,(
    ! [B_429,A_430] :
      ( v1_xboole_0(B_429)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_429),A_430))
      | ~ r1_tarski(k2_relat_1(B_429),A_430)
      | ~ v1_funct_1(B_429)
      | ~ v1_relat_1(B_429) ) ),
    inference(resolution,[status(thm)],[c_4343,c_14])).

tff(c_4467,plain,(
    ! [B_429] :
      ( v1_xboole_0(B_429)
      | ~ v1_xboole_0('#skF_3')
      | ~ r1_tarski(k2_relat_1(B_429),'#skF_3')
      | ~ v1_funct_1(B_429)
      | ~ v1_relat_1(B_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2706,c_4460])).

tff(c_4475,plain,(
    ! [B_431] :
      ( v1_xboole_0(B_431)
      | ~ r1_tarski(k2_relat_1(B_431),'#skF_3')
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2675,c_4467])).

tff(c_4660,plain,(
    ! [A_450] :
      ( v1_xboole_0(k2_funct_1(A_450))
      | ~ r1_tarski(k1_relat_1(A_450),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_450))
      | ~ v1_relat_1(k2_funct_1(A_450))
      | ~ v2_funct_1(A_450)
      | ~ v1_funct_1(A_450)
      | ~ v1_relat_1(A_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4475])).

tff(c_4666,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2708,c_4660])).

tff(c_4668,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_74,c_68,c_166,c_2709,c_4666])).

tff(c_4681,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4668])).

tff(c_4684,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_4681])).

tff(c_4688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_74,c_4684])).

tff(c_4689,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4668])).

tff(c_2703,plain,(
    ! [A_34] :
      ( A_34 = '#skF_3'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_122])).

tff(c_4699,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4689,c_2703])).

tff(c_2818,plain,(
    ! [B_251,A_252] :
      ( B_251 = '#skF_3'
      | A_252 = '#skF_3'
      | k2_zfmisc_1(A_252,B_251) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2685,c_2685,c_8])).

tff(c_2828,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2772,c_2818])).

tff(c_2833,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2828])).

tff(c_2844,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2709])).

tff(c_2848,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2702])).

tff(c_2854,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_74])).

tff(c_2853,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_68])).

tff(c_2850,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_166])).

tff(c_2846,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2707])).

tff(c_3012,plain,(
    ! [A_262] :
      ( k1_relat_1(k2_funct_1(A_262)) = k2_relat_1(A_262)
      | ~ v2_funct_1(A_262)
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_26] :
      ( v1_funct_2(A_26,k1_relat_1(A_26),k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3764,plain,(
    ! [A_354] :
      ( v1_funct_2(k2_funct_1(A_354),k2_relat_1(A_354),k2_relat_1(k2_funct_1(A_354)))
      | ~ v1_funct_1(k2_funct_1(A_354))
      | ~ v1_relat_1(k2_funct_1(A_354))
      | ~ v2_funct_1(A_354)
      | ~ v1_funct_1(A_354)
      | ~ v1_relat_1(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3012,c_54])).

tff(c_3773,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1',k2_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2846,c_3764])).

tff(c_3775,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1',k2_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2854,c_2853,c_2850,c_3773])).

tff(c_3776,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3775])).

tff(c_3779,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_3776])).

tff(c_3783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2854,c_3779])).

tff(c_3785,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3775])).

tff(c_2845,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2708])).

tff(c_2849,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2675])).

tff(c_2842,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2833,c_2706])).

tff(c_3353,plain,(
    ! [B_316,A_317] :
      ( m1_subset_1(B_316,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_316),A_317)))
      | ~ r1_tarski(k2_relat_1(B_316),A_317)
      | ~ v1_funct_1(B_316)
      | ~ v1_relat_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3566,plain,(
    ! [B_332,A_333] :
      ( v1_xboole_0(B_332)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_332),A_333))
      | ~ r1_tarski(k2_relat_1(B_332),A_333)
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332) ) ),
    inference(resolution,[status(thm)],[c_3353,c_14])).

tff(c_3573,plain,(
    ! [B_332] :
      ( v1_xboole_0(B_332)
      | ~ v1_xboole_0('#skF_1')
      | ~ r1_tarski(k2_relat_1(B_332),'#skF_1')
      | ~ v1_funct_1(B_332)
      | ~ v1_relat_1(B_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2842,c_3566])).

tff(c_3581,plain,(
    ! [B_334] :
      ( v1_xboole_0(B_334)
      | ~ r1_tarski(k2_relat_1(B_334),'#skF_1')
      | ~ v1_funct_1(B_334)
      | ~ v1_relat_1(B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2849,c_3573])).

tff(c_3818,plain,(
    ! [A_356] :
      ( v1_xboole_0(k2_funct_1(A_356))
      | ~ r1_tarski(k1_relat_1(A_356),'#skF_1')
      | ~ v1_funct_1(k2_funct_1(A_356))
      | ~ v1_relat_1(k2_funct_1(A_356))
      | ~ v2_funct_1(A_356)
      | ~ v1_funct_1(A_356)
      | ~ v1_relat_1(A_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3581])).

tff(c_3824,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2845,c_3818])).

tff(c_3826,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2848,c_2854,c_2853,c_3785,c_2850,c_2844,c_3824])).

tff(c_2840,plain,(
    ! [A_34] :
      ( A_34 = '#skF_1'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2703])).

tff(c_3835,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3826,c_2840])).

tff(c_2721,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_2841,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2833,c_2721])).

tff(c_2993,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2842,c_2841])).

tff(c_2997,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2993])).

tff(c_3843,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3835,c_2997])).

tff(c_3852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_3843])).

tff(c_3853,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2828])).

tff(c_3868,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3853,c_2721])).

tff(c_3873,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_3868])).

tff(c_4716,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4699,c_3873])).

tff(c_4723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2777,c_4716])).

tff(c_4725,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_4768,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4725,c_14])).

tff(c_5037,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_4829,c_4825,c_4768])).

tff(c_2686,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_2675,c_6])).

tff(c_4832,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | ~ v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_2686])).

tff(c_5046,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5037,c_4832])).

tff(c_4724,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_4834,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4724])).

tff(c_5052,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5046,c_4834])).

tff(c_5103,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5099,c_5052])).

tff(c_5104,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5103,c_5052])).

tff(c_5109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4971,c_5104])).

tff(c_5110,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4820])).

tff(c_5114,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5110,c_4725])).

tff(c_5120,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_5114])).

tff(c_5127,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5120,c_14])).

tff(c_5133,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2675,c_5127])).

tff(c_5147,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5133,c_2686])).

tff(c_5115,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5110,c_4724])).

tff(c_5175,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5147,c_5115])).

tff(c_5503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5498,c_5175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.10  
% 5.70/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.10  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.70/2.10  
% 5.70/2.10  %Foreground sorts:
% 5.70/2.10  
% 5.70/2.10  
% 5.70/2.10  %Background operators:
% 5.70/2.10  
% 5.70/2.10  
% 5.70/2.10  %Foreground operators:
% 5.70/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.70/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.70/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.70/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.70/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.70/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.70/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.70/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.70/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.70/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.70/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.10  
% 5.97/2.13  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.97/2.13  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.97/2.13  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.97/2.13  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.97/2.13  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.97/2.13  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.97/2.13  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.97/2.13  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.97/2.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.97/2.13  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.97/2.13  tff(f_130, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.97/2.13  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.97/2.13  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.97/2.13  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.97/2.13  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.97/2.13  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.13  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_1898, plain, (![C_177, A_178, B_179]: (v1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.97/2.13  tff(c_1915, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1898])).
% 5.97/2.13  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_2028, plain, (![A_191, B_192, C_193]: (k2_relset_1(A_191, B_192, C_193)=k2_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.97/2.13  tff(c_2038, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2028])).
% 5.97/2.13  tff(c_2048, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2038])).
% 5.97/2.13  tff(c_32, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.97/2.13  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.97/2.13  tff(c_141, plain, (![A_41]: (v1_funct_1(k2_funct_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.97/2.13  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_140, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 5.97/2.13  tff(c_144, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_141, c_140])).
% 5.97/2.13  tff(c_147, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_144])).
% 5.97/2.13  tff(c_148, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.97/2.13  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_148])).
% 5.97/2.13  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_155])).
% 5.97/2.13  tff(c_165, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 5.97/2.13  tff(c_178, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_182, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_178])).
% 5.97/2.13  tff(c_193, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.97/2.13  tff(c_206, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_193])).
% 5.97/2.13  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.97/2.13  tff(c_357, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.97/2.13  tff(c_372, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_357])).
% 5.97/2.13  tff(c_705, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.97/2.13  tff(c_721, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_705])).
% 5.97/2.13  tff(c_736, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_372, c_721])).
% 5.97/2.13  tff(c_738, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_736])).
% 5.97/2.13  tff(c_30, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.97/2.13  tff(c_28, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.97/2.13  tff(c_166, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 5.97/2.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.97/2.13  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_591, plain, (![B_97, A_98]: (m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97), A_98))) | ~r1_tarski(k2_relat_1(B_97), A_98) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.97/2.13  tff(c_14, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.97/2.13  tff(c_1131, plain, (![B_135, A_136]: (v1_xboole_0(B_135) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_135), A_136)) | ~r1_tarski(k2_relat_1(B_135), A_136) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_591, c_14])).
% 5.97/2.13  tff(c_1141, plain, (![B_135]: (v1_xboole_0(B_135) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(B_135), k1_xboole_0) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1131])).
% 5.97/2.13  tff(c_1170, plain, (![B_139]: (v1_xboole_0(B_139) | ~r1_tarski(k2_relat_1(B_139), k1_xboole_0) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1141])).
% 5.97/2.13  tff(c_1360, plain, (![A_155]: (v1_xboole_0(k2_funct_1(A_155)) | ~r1_tarski(k1_relat_1(A_155), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_155)) | ~v1_relat_1(k2_funct_1(A_155)) | ~v2_funct_1(A_155) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1170])).
% 5.97/2.13  tff(c_1363, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_738, c_1360])).
% 5.97/2.13  tff(c_1371, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_74, c_68, c_166, c_1363])).
% 5.97/2.13  tff(c_1374, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1371])).
% 5.97/2.13  tff(c_1377, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1374])).
% 5.97/2.13  tff(c_1381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_74, c_1377])).
% 5.97/2.13  tff(c_1383, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1371])).
% 5.97/2.13  tff(c_322, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.97/2.13  tff(c_329, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_322])).
% 5.97/2.13  tff(c_338, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_329])).
% 5.97/2.13  tff(c_390, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.97/2.13  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.97/2.13  tff(c_639, plain, (![A_103]: (r1_tarski(A_103, k2_zfmisc_1(k1_relat_1(A_103), k2_relat_1(A_103))) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_390, c_16])).
% 5.97/2.13  tff(c_1453, plain, (![A_159]: (r1_tarski(k2_funct_1(A_159), k2_zfmisc_1(k2_relat_1(A_159), k2_relat_1(k2_funct_1(A_159)))) | ~v1_funct_1(k2_funct_1(A_159)) | ~v1_relat_1(k2_funct_1(A_159)) | ~v2_funct_1(A_159) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_32, c_639])).
% 5.97/2.13  tff(c_1474, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_338, c_1453])).
% 5.97/2.13  tff(c_1491, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_74, c_68, c_1383, c_166, c_1474])).
% 5.97/2.13  tff(c_1514, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1491])).
% 5.97/2.13  tff(c_1526, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_74, c_68, c_738, c_1514])).
% 5.97/2.13  tff(c_1528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1526])).
% 5.97/2.13  tff(c_1529, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_736])).
% 5.97/2.13  tff(c_1560, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_2])).
% 5.97/2.13  tff(c_1556, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_1529, c_10])).
% 5.97/2.13  tff(c_408, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_338, c_390])).
% 5.97/2.13  tff(c_427, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_74, c_408])).
% 5.97/2.13  tff(c_452, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_427, c_14])).
% 5.97/2.13  tff(c_471, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_452])).
% 5.97/2.13  tff(c_1672, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1556, c_471])).
% 5.97/2.13  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1672])).
% 5.97/2.13  tff(c_1681, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_452])).
% 5.97/2.13  tff(c_119, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.97/2.13  tff(c_122, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_2, c_119])).
% 5.97/2.13  tff(c_1691, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1681, c_122])).
% 5.97/2.13  tff(c_1709, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_1691, c_10])).
% 5.97/2.13  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.97/2.13  tff(c_1710, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_1691, c_20])).
% 5.97/2.13  tff(c_1721, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1710, c_338])).
% 5.97/2.13  tff(c_168, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.97/2.13  tff(c_176, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_168])).
% 5.97/2.13  tff(c_177, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_176])).
% 5.97/2.13  tff(c_1744, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_177])).
% 5.97/2.13  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1709, c_1744])).
% 5.97/2.13  tff(c_1862, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_1863, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_2141, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.97/2.13  tff(c_2166, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1863, c_2141])).
% 5.97/2.13  tff(c_2453, plain, (![B_236, C_237, A_238]: (k1_xboole_0=B_236 | v1_funct_2(C_237, A_238, B_236) | k1_relset_1(A_238, B_236, C_237)!=A_238 | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_236))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.97/2.13  tff(c_2465, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1863, c_2453])).
% 5.97/2.13  tff(c_2485, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2166, c_2465])).
% 5.97/2.13  tff(c_2486, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1862, c_2485])).
% 5.97/2.13  tff(c_2491, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2486])).
% 5.97/2.13  tff(c_2494, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_2491])).
% 5.97/2.13  tff(c_2497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1915, c_74, c_68, c_2048, c_2494])).
% 5.97/2.13  tff(c_2498, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2486])).
% 5.97/2.13  tff(c_2527, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2])).
% 5.97/2.13  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_2522, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2498, c_2498, c_12])).
% 5.97/2.13  tff(c_2669, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_177])).
% 5.97/2.13  tff(c_2674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2527, c_2669])).
% 5.97/2.13  tff(c_2675, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_176])).
% 5.97/2.13  tff(c_2685, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2675, c_122])).
% 5.97/2.13  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.97/2.13  tff(c_2708, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_22])).
% 5.97/2.13  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.97/2.13  tff(c_2709, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_4])).
% 5.97/2.13  tff(c_5288, plain, (![A_486, B_487, C_488]: (k1_relset_1(A_486, B_487, C_488)=k1_relat_1(C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.97/2.13  tff(c_5352, plain, (![A_499, B_500, A_501]: (k1_relset_1(A_499, B_500, A_501)=k1_relat_1(A_501) | ~r1_tarski(A_501, k2_zfmisc_1(A_499, B_500)))), inference(resolution, [status(thm)], [c_18, c_5288])).
% 5.97/2.13  tff(c_5362, plain, (![A_499, B_500]: (k1_relset_1(A_499, B_500, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2709, c_5352])).
% 5.97/2.13  tff(c_5364, plain, (![A_499, B_500]: (k1_relset_1(A_499, B_500, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2708, c_5362])).
% 5.97/2.13  tff(c_2676, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_176])).
% 5.97/2.13  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.97/2.13  tff(c_4748, plain, (![A_455]: (A_455='#skF_3' | ~v1_xboole_0(A_455))), inference(resolution, [status(thm)], [c_2675, c_6])).
% 5.97/2.13  tff(c_4755, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_2676, c_4748])).
% 5.97/2.13  tff(c_4789, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4755, c_70])).
% 5.97/2.13  tff(c_44, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.97/2.13  tff(c_76, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 5.97/2.13  tff(c_5490, plain, (![C_521, B_522]: (v1_funct_2(C_521, '#skF_3', B_522) | k1_relset_1('#skF_3', B_522, C_521)!='#skF_3' | ~m1_subset_1(C_521, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_2685, c_2685, c_76])).
% 5.97/2.13  tff(c_5492, plain, (![B_522]: (v1_funct_2('#skF_3', '#skF_3', B_522) | k1_relset_1('#skF_3', B_522, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_4789, c_5490])).
% 5.97/2.13  tff(c_5498, plain, (![B_522]: (v1_funct_2('#skF_3', '#skF_3', B_522))), inference(demodulation, [status(thm), theory('equality')], [c_5364, c_5492])).
% 5.97/2.13  tff(c_2705, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_12])).
% 5.97/2.13  tff(c_8, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_4810, plain, (![B_457, A_458]: (B_457='#skF_3' | A_458='#skF_3' | k2_zfmisc_1(A_458, B_457)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_2685, c_8])).
% 5.97/2.13  tff(c_4820, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4755, c_4810])).
% 5.97/2.13  tff(c_4825, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_4820])).
% 5.97/2.13  tff(c_2689, plain, (![C_242, A_243, B_244]: (v1_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.97/2.13  tff(c_2702, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2689])).
% 5.97/2.13  tff(c_4839, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_2702])).
% 5.97/2.13  tff(c_4845, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_74])).
% 5.97/2.13  tff(c_2707, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_20])).
% 5.97/2.13  tff(c_4837, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4825, c_2707])).
% 5.97/2.13  tff(c_4836, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4825, c_2708])).
% 5.97/2.13  tff(c_4963, plain, (![A_466]: (v1_funct_2(A_466, k1_relat_1(A_466), k2_relat_1(A_466)) | ~v1_funct_1(A_466) | ~v1_relat_1(A_466))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.97/2.13  tff(c_4966, plain, (v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4836, c_4963])).
% 5.97/2.13  tff(c_4971, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4839, c_4845, c_4837, c_4966])).
% 5.97/2.13  tff(c_4827, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4825, c_4789])).
% 5.97/2.13  tff(c_4838, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_2685])).
% 5.97/2.13  tff(c_40, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.97/2.13  tff(c_77, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 5.97/2.13  tff(c_4867, plain, (![A_23]: (v1_funct_2('#skF_1', A_23, '#skF_1') | A_23='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4838, c_4838, c_4838, c_4838, c_4838, c_77])).
% 5.97/2.13  tff(c_4868, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4867])).
% 5.97/2.13  tff(c_4929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4827, c_4868])).
% 5.97/2.13  tff(c_5099, plain, (![A_472]: (v1_funct_2('#skF_1', A_472, '#skF_1') | A_472='#skF_1')), inference(splitRight, [status(thm)], [c_4867])).
% 5.97/2.13  tff(c_4840, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_2675])).
% 5.97/2.13  tff(c_2706, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_10])).
% 5.97/2.13  tff(c_4829, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4825, c_2706])).
% 5.97/2.13  tff(c_2765, plain, (![A_248]: (A_248='#skF_3' | ~v1_xboole_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_122])).
% 5.97/2.13  tff(c_2772, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_2676, c_2765])).
% 5.97/2.13  tff(c_2777, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2772, c_70])).
% 5.97/2.13  tff(c_4343, plain, (![B_418, A_419]: (m1_subset_1(B_418, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_418), A_419))) | ~r1_tarski(k2_relat_1(B_418), A_419) | ~v1_funct_1(B_418) | ~v1_relat_1(B_418))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.97/2.13  tff(c_4460, plain, (![B_429, A_430]: (v1_xboole_0(B_429) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_429), A_430)) | ~r1_tarski(k2_relat_1(B_429), A_430) | ~v1_funct_1(B_429) | ~v1_relat_1(B_429))), inference(resolution, [status(thm)], [c_4343, c_14])).
% 5.97/2.13  tff(c_4467, plain, (![B_429]: (v1_xboole_0(B_429) | ~v1_xboole_0('#skF_3') | ~r1_tarski(k2_relat_1(B_429), '#skF_3') | ~v1_funct_1(B_429) | ~v1_relat_1(B_429))), inference(superposition, [status(thm), theory('equality')], [c_2706, c_4460])).
% 5.97/2.13  tff(c_4475, plain, (![B_431]: (v1_xboole_0(B_431) | ~r1_tarski(k2_relat_1(B_431), '#skF_3') | ~v1_funct_1(B_431) | ~v1_relat_1(B_431))), inference(demodulation, [status(thm), theory('equality')], [c_2675, c_4467])).
% 5.97/2.13  tff(c_4660, plain, (![A_450]: (v1_xboole_0(k2_funct_1(A_450)) | ~r1_tarski(k1_relat_1(A_450), '#skF_3') | ~v1_funct_1(k2_funct_1(A_450)) | ~v1_relat_1(k2_funct_1(A_450)) | ~v2_funct_1(A_450) | ~v1_funct_1(A_450) | ~v1_relat_1(A_450))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4475])).
% 5.97/2.13  tff(c_4666, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2708, c_4660])).
% 5.97/2.13  tff(c_4668, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_74, c_68, c_166, c_2709, c_4666])).
% 5.97/2.13  tff(c_4681, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4668])).
% 5.97/2.13  tff(c_4684, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_4681])).
% 5.97/2.13  tff(c_4688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2702, c_74, c_4684])).
% 5.97/2.13  tff(c_4689, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4668])).
% 5.97/2.13  tff(c_2703, plain, (![A_34]: (A_34='#skF_3' | ~v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_122])).
% 5.97/2.13  tff(c_4699, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4689, c_2703])).
% 5.97/2.13  tff(c_2818, plain, (![B_251, A_252]: (B_251='#skF_3' | A_252='#skF_3' | k2_zfmisc_1(A_252, B_251)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2685, c_2685, c_8])).
% 5.97/2.13  tff(c_2828, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2772, c_2818])).
% 5.97/2.13  tff(c_2833, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_2828])).
% 5.97/2.13  tff(c_2844, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2709])).
% 5.97/2.13  tff(c_2848, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2702])).
% 5.97/2.13  tff(c_2854, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_74])).
% 5.97/2.13  tff(c_2853, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_68])).
% 5.97/2.13  tff(c_2850, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_166])).
% 5.97/2.13  tff(c_2846, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2707])).
% 5.97/2.13  tff(c_3012, plain, (![A_262]: (k1_relat_1(k2_funct_1(A_262))=k2_relat_1(A_262) | ~v2_funct_1(A_262) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.97/2.13  tff(c_54, plain, (![A_26]: (v1_funct_2(A_26, k1_relat_1(A_26), k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.97/2.13  tff(c_3764, plain, (![A_354]: (v1_funct_2(k2_funct_1(A_354), k2_relat_1(A_354), k2_relat_1(k2_funct_1(A_354))) | ~v1_funct_1(k2_funct_1(A_354)) | ~v1_relat_1(k2_funct_1(A_354)) | ~v2_funct_1(A_354) | ~v1_funct_1(A_354) | ~v1_relat_1(A_354))), inference(superposition, [status(thm), theory('equality')], [c_3012, c_54])).
% 5.97/2.13  tff(c_3773, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', k2_relat_1(k2_funct_1('#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2846, c_3764])).
% 5.97/2.13  tff(c_3775, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', k2_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2848, c_2854, c_2853, c_2850, c_3773])).
% 5.97/2.13  tff(c_3776, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_3775])).
% 5.97/2.13  tff(c_3779, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_3776])).
% 5.97/2.13  tff(c_3783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2848, c_2854, c_3779])).
% 5.97/2.13  tff(c_3785, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3775])).
% 5.97/2.13  tff(c_2845, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2708])).
% 5.97/2.13  tff(c_2849, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2675])).
% 5.97/2.13  tff(c_2842, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2833, c_2706])).
% 5.97/2.13  tff(c_3353, plain, (![B_316, A_317]: (m1_subset_1(B_316, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_316), A_317))) | ~r1_tarski(k2_relat_1(B_316), A_317) | ~v1_funct_1(B_316) | ~v1_relat_1(B_316))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.97/2.13  tff(c_3566, plain, (![B_332, A_333]: (v1_xboole_0(B_332) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_332), A_333)) | ~r1_tarski(k2_relat_1(B_332), A_333) | ~v1_funct_1(B_332) | ~v1_relat_1(B_332))), inference(resolution, [status(thm)], [c_3353, c_14])).
% 5.97/2.13  tff(c_3573, plain, (![B_332]: (v1_xboole_0(B_332) | ~v1_xboole_0('#skF_1') | ~r1_tarski(k2_relat_1(B_332), '#skF_1') | ~v1_funct_1(B_332) | ~v1_relat_1(B_332))), inference(superposition, [status(thm), theory('equality')], [c_2842, c_3566])).
% 5.97/2.13  tff(c_3581, plain, (![B_334]: (v1_xboole_0(B_334) | ~r1_tarski(k2_relat_1(B_334), '#skF_1') | ~v1_funct_1(B_334) | ~v1_relat_1(B_334))), inference(demodulation, [status(thm), theory('equality')], [c_2849, c_3573])).
% 5.97/2.13  tff(c_3818, plain, (![A_356]: (v1_xboole_0(k2_funct_1(A_356)) | ~r1_tarski(k1_relat_1(A_356), '#skF_1') | ~v1_funct_1(k2_funct_1(A_356)) | ~v1_relat_1(k2_funct_1(A_356)) | ~v2_funct_1(A_356) | ~v1_funct_1(A_356) | ~v1_relat_1(A_356))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3581])).
% 5.97/2.13  tff(c_3824, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2845, c_3818])).
% 5.97/2.13  tff(c_3826, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2848, c_2854, c_2853, c_3785, c_2850, c_2844, c_3824])).
% 5.97/2.13  tff(c_2840, plain, (![A_34]: (A_34='#skF_1' | ~v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2703])).
% 5.97/2.13  tff(c_3835, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3826, c_2840])).
% 5.97/2.13  tff(c_2721, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_2841, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2833, c_2721])).
% 5.97/2.13  tff(c_2993, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2842, c_2841])).
% 5.97/2.13  tff(c_2997, plain, (~r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_18, c_2993])).
% 5.97/2.13  tff(c_3843, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3835, c_2997])).
% 5.97/2.13  tff(c_3852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2844, c_3843])).
% 5.97/2.13  tff(c_3853, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_2828])).
% 5.97/2.13  tff(c_3868, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3853, c_2721])).
% 5.97/2.13  tff(c_3873, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_3868])).
% 5.97/2.13  tff(c_4716, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4699, c_3873])).
% 5.97/2.13  tff(c_4723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2777, c_4716])).
% 5.97/2.13  tff(c_4725, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_4768, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_4725, c_14])).
% 5.97/2.13  tff(c_5037, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_4829, c_4825, c_4768])).
% 5.97/2.13  tff(c_2686, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_2675, c_6])).
% 5.97/2.13  tff(c_4832, plain, (![A_2]: (A_2='#skF_1' | ~v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_2686])).
% 5.97/2.13  tff(c_5046, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_5037, c_4832])).
% 5.97/2.13  tff(c_4724, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_165])).
% 5.97/2.13  tff(c_4834, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4724])).
% 5.97/2.13  tff(c_5052, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5046, c_4834])).
% 5.97/2.13  tff(c_5103, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5099, c_5052])).
% 5.97/2.13  tff(c_5104, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5103, c_5052])).
% 5.97/2.13  tff(c_5109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4971, c_5104])).
% 5.97/2.13  tff(c_5110, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4820])).
% 5.97/2.13  tff(c_5114, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5110, c_4725])).
% 5.97/2.13  tff(c_5120, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_5114])).
% 5.97/2.13  tff(c_5127, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5120, c_14])).
% 5.97/2.13  tff(c_5133, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2675, c_5127])).
% 5.97/2.13  tff(c_5147, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5133, c_2686])).
% 5.97/2.13  tff(c_5115, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5110, c_4724])).
% 5.97/2.13  tff(c_5175, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5147, c_5115])).
% 5.97/2.13  tff(c_5503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5498, c_5175])).
% 5.97/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.13  
% 5.97/2.13  Inference rules
% 5.97/2.13  ----------------------
% 5.97/2.13  #Ref     : 0
% 5.97/2.13  #Sup     : 1169
% 5.97/2.13  #Fact    : 0
% 5.97/2.13  #Define  : 0
% 5.97/2.13  #Split   : 24
% 5.97/2.13  #Chain   : 0
% 5.97/2.13  #Close   : 0
% 5.97/2.13  
% 5.97/2.13  Ordering : KBO
% 5.97/2.13  
% 5.97/2.13  Simplification rules
% 5.97/2.14  ----------------------
% 5.97/2.14  #Subsume      : 161
% 5.97/2.14  #Demod        : 1476
% 5.97/2.14  #Tautology    : 658
% 5.97/2.14  #SimpNegUnit  : 6
% 5.97/2.14  #BackRed      : 203
% 5.97/2.14  
% 5.97/2.14  #Partial instantiations: 0
% 5.97/2.14  #Strategies tried      : 1
% 5.97/2.14  
% 5.97/2.14  Timing (in seconds)
% 5.97/2.14  ----------------------
% 5.97/2.14  Preprocessing        : 0.35
% 5.97/2.14  Parsing              : 0.18
% 5.97/2.14  CNF conversion       : 0.02
% 5.97/2.14  Main loop            : 0.97
% 5.97/2.14  Inferencing          : 0.35
% 5.97/2.14  Reduction            : 0.33
% 5.97/2.14  Demodulation         : 0.24
% 5.97/2.14  BG Simplification    : 0.04
% 5.97/2.14  Subsumption          : 0.16
% 5.97/2.14  Abstraction          : 0.04
% 5.97/2.14  MUC search           : 0.00
% 5.97/2.14  Cooper               : 0.00
% 5.97/2.14  Total                : 1.41
% 5.97/2.14  Index Insertion      : 0.00
% 5.97/2.14  Index Deletion       : 0.00
% 5.97/2.14  Index Matching       : 0.00
% 5.97/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
