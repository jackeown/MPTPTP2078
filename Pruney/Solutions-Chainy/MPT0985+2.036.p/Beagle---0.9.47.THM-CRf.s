%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:31 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  310 (7573 expanded)
%              Number of leaves         :   40 (2491 expanded)
%              Depth                    :   22
%              Number of atoms          :  580 (18881 expanded)
%              Number of equality atoms :  146 (5169 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_155,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_325,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_partfun1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_344,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_325])).

tff(c_348,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_470,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_493,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_470])).

tff(c_2209,plain,(
    ! [B_251,A_252,C_253] :
      ( k1_xboole_0 = B_251
      | k1_relset_1(A_252,B_251,C_253) = A_252
      | ~ v1_funct_2(C_253,A_252,B_251)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2222,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2209])).

tff(c_2240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_493,c_2222])).

tff(c_2244,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2240])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_134,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_133,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_137,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_133])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_137])).

tff(c_152,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_159,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_152])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_159])).

tff(c_173,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_187,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_187])).

tff(c_70,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_516,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_526,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_516])).

tff(c_540,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_526])).

tff(c_34,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_174,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_361,plain,(
    ! [A_86] :
      ( k1_relat_1(k2_funct_1(A_86)) = k2_relat_1(A_86)
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1430,plain,(
    ! [A_201] :
      ( v1_funct_2(k2_funct_1(A_201),k2_relat_1(A_201),k2_relat_1(k2_funct_1(A_201)))
      | ~ v1_funct_1(k2_funct_1(A_201))
      | ~ v1_relat_1(k2_funct_1(A_201))
      | ~ v2_funct_1(A_201)
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_62])).

tff(c_1433,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_1430])).

tff(c_1441,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_174,c_1433])).

tff(c_1442,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1441])).

tff(c_1445,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1442])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_1445])).

tff(c_1451,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1441])).

tff(c_881,plain,(
    ! [B_154,A_155,C_156] :
      ( k1_xboole_0 = B_154
      | k1_relset_1(A_155,B_154,C_156) = A_155
      | ~ v1_funct_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_894,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_881])).

tff(c_912,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_493,c_894])).

tff(c_916,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_912])).

tff(c_32,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_414,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96))))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1533,plain,(
    ! [A_208] :
      ( m1_subset_1(k2_funct_1(A_208),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_208)),k1_relat_1(A_208))))
      | ~ v1_funct_1(k2_funct_1(A_208))
      | ~ v1_relat_1(k2_funct_1(A_208))
      | ~ v2_funct_1(A_208)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_414])).

tff(c_1565,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_1533])).

tff(c_1586,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_1451,c_174,c_1565])).

tff(c_1620,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1586])).

tff(c_1639,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_540,c_1620])).

tff(c_1641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_1639])).

tff(c_1642,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_912])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1675,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1642,c_8])).

tff(c_124,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_113])).

tff(c_1752,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_124])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1902,plain,(
    ! [A_217] :
      ( A_217 = '#skF_3'
      | ~ r1_tarski(A_217,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1642,c_4])).

tff(c_1910,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1752,c_1902])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1678,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_2])).

tff(c_1927,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1678])).

tff(c_494,plain,(
    ! [A_101,B_102] : k1_relset_1(A_101,B_102,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_470])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_613,plain,(
    ! [C_113,B_114] :
      ( v1_funct_2(C_113,k1_xboole_0,B_114)
      | k1_relset_1(k1_xboole_0,B_114,C_113) != k1_xboole_0
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_619,plain,(
    ! [B_114] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_114)
      | k1_relset_1(k1_xboole_0,B_114,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_613])).

tff(c_622,plain,(
    ! [B_114] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_114)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_619])).

tff(c_627,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_342,plain,(
    ! [C_81] :
      ( v1_partfun1(C_81,k1_xboole_0)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_325])).

tff(c_350,plain,(
    ! [C_85] :
      ( v1_partfun1(C_85,k1_xboole_0)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_342])).

tff(c_360,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_350])).

tff(c_260,plain,(
    ! [B_73,A_74] :
      ( v1_funct_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_273,plain,(
    ! [A_4] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_260])).

tff(c_298,plain,(
    ! [A_78] :
      ( ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_304,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_204,c_298])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_304])).

tff(c_313,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_675,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_funct_2(C_126,A_127,B_128)
      | ~ v1_partfun1(C_126,A_127)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_695,plain,(
    ! [A_127,B_128] :
      ( v1_funct_2(k1_xboole_0,A_127,B_128)
      | ~ v1_partfun1(k1_xboole_0,A_127)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_675])).

tff(c_710,plain,(
    ! [A_129,B_130] :
      ( v1_funct_2(k1_xboole_0,A_129,B_130)
      | ~ v1_partfun1(k1_xboole_0,A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_695])).

tff(c_56,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_79,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_713,plain,(
    ! [B_130] :
      ( k1_relset_1(k1_xboole_0,B_130,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_710,c_79])).

tff(c_719,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_12,c_494,c_713])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_627,c_719])).

tff(c_723,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_1655,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1642,c_723])).

tff(c_1924,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1910,c_1655])).

tff(c_60,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_548,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_60])).

tff(c_557,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_548])).

tff(c_46,plain,(
    ! [C_30,A_27,B_28] :
      ( v1_partfun1(C_30,A_27)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_605,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_557,c_46])).

tff(c_782,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_1993,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1924,c_782])).

tff(c_1996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1993])).

tff(c_1998,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_2247,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_1998])).

tff(c_2255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_2247])).

tff(c_2256,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2240])).

tff(c_2292,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_8])).

tff(c_2441,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_124])).

tff(c_2508,plain,(
    ! [A_261] :
      ( A_261 = '#skF_3'
      | ~ r1_tarski(A_261,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_4])).

tff(c_2516,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2441,c_2508])).

tff(c_2294,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_10])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_2395,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_258])).

tff(c_2526,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2395])).

tff(c_2540,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_540])).

tff(c_3480,plain,(
    ! [A_353] :
      ( v1_funct_2(k2_funct_1(A_353),k2_relat_1(A_353),k2_relat_1(k2_funct_1(A_353)))
      | ~ v1_funct_1(k2_funct_1(A_353))
      | ~ v1_relat_1(k2_funct_1(A_353))
      | ~ v2_funct_1(A_353)
      | ~ v1_funct_1(A_353)
      | ~ v1_relat_1(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_62])).

tff(c_3483,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2540,c_3480])).

tff(c_3491,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_174,c_3483])).

tff(c_3492,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3491])).

tff(c_3495,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_3492])).

tff(c_3499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_3495])).

tff(c_3501,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3491])).

tff(c_2525,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2516,c_2292])).

tff(c_2272,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_723])).

tff(c_2531,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_2516,c_2272])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_444,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,k2_zfmisc_1(k1_relat_1(A_98),k2_relat_1(A_98)))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_414,c_14])).

tff(c_3573,plain,(
    ! [A_359] :
      ( r1_tarski(k2_funct_1(A_359),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_359)),k1_relat_1(A_359)))
      | ~ v1_funct_1(k2_funct_1(A_359))
      | ~ v1_relat_1(k2_funct_1(A_359))
      | ~ v2_funct_1(A_359)
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_444])).

tff(c_3600,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2531,c_3573])).

tff(c_3616,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_3501,c_174,c_2525,c_3600])).

tff(c_3618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2526,c_3616])).

tff(c_3620,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_3646,plain,(
    ! [C_364,A_365] :
      ( v1_partfun1(C_364,A_365)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(A_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_325])).

tff(c_3653,plain,(
    ! [A_5,A_365] :
      ( v1_partfun1(A_5,A_365)
      | ~ v1_xboole_0(A_365)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3646])).

tff(c_4524,plain,(
    ! [C_439,A_440,B_441] :
      ( v1_funct_2(C_439,A_440,B_441)
      | ~ v1_partfun1(C_439,A_440)
      | ~ v1_funct_1(C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4544,plain,(
    ! [A_440,B_441] :
      ( v1_funct_2(k1_xboole_0,A_440,B_441)
      | ~ v1_partfun1(k1_xboole_0,A_440)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_4524])).

tff(c_4558,plain,(
    ! [A_440,B_441] :
      ( v1_funct_2(k1_xboole_0,A_440,B_441)
      | ~ v1_partfun1(k1_xboole_0,A_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_4544])).

tff(c_3622,plain,(
    ! [C_361] :
      ( v1_partfun1(C_361,k1_xboole_0)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_342])).

tff(c_3632,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_3622])).

tff(c_3744,plain,(
    ! [A_377,B_378,C_379] :
      ( k1_relset_1(A_377,B_378,C_379) = k1_relat_1(C_379)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3768,plain,(
    ! [A_377,B_378] : k1_relset_1(A_377,B_378,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_3744])).

tff(c_4559,plain,(
    ! [A_442,B_443] :
      ( v1_funct_2(k1_xboole_0,A_442,B_443)
      | ~ v1_partfun1(k1_xboole_0,A_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_4544])).

tff(c_4562,plain,(
    ! [B_443] :
      ( k1_relset_1(k1_xboole_0,B_443,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4559,c_79])).

tff(c_4568,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3632,c_12,c_3768,c_4562])).

tff(c_4573,plain,(
    ! [A_377,B_378] : k1_relset_1(A_377,B_378,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_3768])).

tff(c_4657,plain,(
    ! [B_455,A_456,C_457] :
      ( k1_xboole_0 = B_455
      | k1_relset_1(A_456,B_455,C_457) = A_456
      | ~ v1_funct_2(C_457,A_456,B_455)
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_zfmisc_1(A_456,B_455))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4677,plain,(
    ! [B_455,A_456] :
      ( k1_xboole_0 = B_455
      | k1_relset_1(A_456,B_455,k1_xboole_0) = A_456
      | ~ v1_funct_2(k1_xboole_0,A_456,B_455) ) ),
    inference(resolution,[status(thm)],[c_12,c_4657])).

tff(c_4737,plain,(
    ! [B_458,A_459] :
      ( k1_xboole_0 = B_458
      | k1_xboole_0 = A_459
      | ~ v1_funct_2(k1_xboole_0,A_459,B_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_4677])).

tff(c_4753,plain,(
    ! [B_441,A_440] :
      ( k1_xboole_0 = B_441
      | k1_xboole_0 = A_440
      | ~ v1_partfun1(k1_xboole_0,A_440) ) ),
    inference(resolution,[status(thm)],[c_4558,c_4737])).

tff(c_4789,plain,(
    ! [A_463] :
      ( k1_xboole_0 = A_463
      | ~ v1_partfun1(k1_xboole_0,A_463) ) ),
    inference(splitLeft,[status(thm)],[c_4753])).

tff(c_4797,plain,(
    ! [A_365] :
      ( k1_xboole_0 = A_365
      | ~ v1_xboole_0(A_365)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3653,c_4789])).

tff(c_4821,plain,(
    ! [A_464] :
      ( k1_xboole_0 = A_464
      | ~ v1_xboole_0(A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_4797])).

tff(c_4828,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3620,c_4821])).

tff(c_4865,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_2',B_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_4828,c_10])).

tff(c_5004,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4865,c_124])).

tff(c_5100,plain,(
    ! [A_477] :
      ( A_477 = '#skF_2'
      | ~ r1_tarski(A_477,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_4828,c_4])).

tff(c_5108,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5004,c_5100])).

tff(c_4863,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_4828,c_8])).

tff(c_4976,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_254])).

tff(c_5114,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5108,c_4976])).

tff(c_4842,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4828,c_4828,c_4568])).

tff(c_5127,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5108,c_5108,c_4842])).

tff(c_3676,plain,(
    ! [A_371] :
      ( k2_relat_1(k2_funct_1(A_371)) = k1_relat_1(A_371)
      | ~ v2_funct_1(A_371)
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5855,plain,(
    ! [A_559] :
      ( v1_funct_2(k2_funct_1(A_559),k1_relat_1(k2_funct_1(A_559)),k1_relat_1(A_559))
      | ~ v1_funct_1(k2_funct_1(A_559))
      | ~ v1_relat_1(k2_funct_1(A_559))
      | ~ v2_funct_1(A_559)
      | ~ v1_funct_1(A_559)
      | ~ v1_relat_1(A_559) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3676,c_62])).

tff(c_5858,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5127,c_5855])).

tff(c_5866,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_174,c_5858])).

tff(c_5867,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5866])).

tff(c_5870,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_5867])).

tff(c_5874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_5870])).

tff(c_5876,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5866])).

tff(c_5121,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5108,c_5108,c_4863])).

tff(c_3695,plain,(
    ! [A_374] :
      ( m1_subset_1(A_374,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_374),k2_relat_1(A_374))))
      | ~ v1_funct_1(A_374)
      | ~ v1_relat_1(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6160,plain,(
    ! [A_586] :
      ( m1_subset_1(k2_funct_1(A_586),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_586)),k1_relat_1(A_586))))
      | ~ v1_funct_1(k2_funct_1(A_586))
      | ~ v1_relat_1(k2_funct_1(A_586))
      | ~ v2_funct_1(A_586)
      | ~ v1_funct_1(A_586)
      | ~ v1_relat_1(A_586) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3695])).

tff(c_6192,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5127,c_6160])).

tff(c_6210,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_5876,c_174,c_5121,c_6192])).

tff(c_6212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5114,c_6210])).

tff(c_6214,plain,(
    ! [B_587] : k1_xboole_0 = B_587 ),
    inference(splitRight,[status(thm)],[c_4753])).

tff(c_6437,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6214,c_258])).

tff(c_6545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_6437])).

tff(c_6546,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_6547,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_6644,plain,(
    ! [C_1401,A_1402,B_1403] :
      ( v1_partfun1(C_1401,A_1402)
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k2_zfmisc_1(A_1402,B_1403)))
      | ~ v1_xboole_0(A_1402) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6665,plain,
    ( v1_partfun1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6547,c_6644])).

tff(c_7442,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6665])).

tff(c_6667,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_6644])).

tff(c_6671,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6667])).

tff(c_6736,plain,(
    ! [A_1416,B_1417,C_1418] :
      ( k2_relset_1(A_1416,B_1417,C_1418) = k2_relat_1(C_1418)
      | ~ m1_subset_1(C_1418,k1_zfmisc_1(k2_zfmisc_1(A_1416,B_1417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6746,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6736])).

tff(c_6760,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6746])).

tff(c_6674,plain,(
    ! [A_1405,B_1406,C_1407] :
      ( k1_relset_1(A_1405,B_1406,C_1407) = k1_relat_1(C_1407)
      | ~ m1_subset_1(C_1407,k1_zfmisc_1(k2_zfmisc_1(A_1405,B_1406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6695,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6547,c_6674])).

tff(c_7317,plain,(
    ! [B_1469,C_1470,A_1471] :
      ( k1_xboole_0 = B_1469
      | v1_funct_2(C_1470,A_1471,B_1469)
      | k1_relset_1(A_1471,B_1469,C_1470) != A_1471
      | ~ m1_subset_1(C_1470,k1_zfmisc_1(k2_zfmisc_1(A_1471,B_1469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7326,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6547,c_7317])).

tff(c_7349,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6695,c_7326])).

tff(c_7350,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6546,c_7349])).

tff(c_7357,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7350])).

tff(c_7360,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7357])).

tff(c_7363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_6760,c_7360])).

tff(c_7364,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7350])).

tff(c_7400,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_2])).

tff(c_7402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6671,c_7400])).

tff(c_7404,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6667])).

tff(c_6668,plain,(
    ! [A_1402] :
      ( v1_partfun1(k1_xboole_0,A_1402)
      | ~ v1_xboole_0(A_1402) ) ),
    inference(resolution,[status(thm)],[c_12,c_6644])).

tff(c_36,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6557,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6547,c_36])).

tff(c_6565,plain,(
    ! [B_1393,A_1394] :
      ( v1_funct_1(B_1393)
      | ~ m1_subset_1(B_1393,k1_zfmisc_1(A_1394))
      | ~ v1_funct_1(A_1394)
      | ~ v1_relat_1(A_1394) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6583,plain,(
    ! [A_4] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_6565])).

tff(c_6585,plain,(
    ! [A_1395] :
      ( ~ v1_funct_1(A_1395)
      | ~ v1_relat_1(A_1395) ) ),
    inference(splitLeft,[status(thm)],[c_6583])).

tff(c_6588,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6557,c_6585])).

tff(c_6601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_6588])).

tff(c_6602,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6583])).

tff(c_7944,plain,(
    ! [C_1536,A_1537,B_1538] :
      ( v1_funct_2(C_1536,A_1537,B_1538)
      | ~ v1_partfun1(C_1536,A_1537)
      | ~ v1_funct_1(C_1536)
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(A_1537,B_1538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7967,plain,(
    ! [A_1537,B_1538] :
      ( v1_funct_2(k1_xboole_0,A_1537,B_1538)
      | ~ v1_partfun1(k1_xboole_0,A_1537)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_7944])).

tff(c_7985,plain,(
    ! [A_1537,B_1538] :
      ( v1_funct_2(k1_xboole_0,A_1537,B_1538)
      | ~ v1_partfun1(k1_xboole_0,A_1537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6602,c_7967])).

tff(c_7405,plain,(
    ! [A_1472,B_1473,C_1474] :
      ( k1_relset_1(A_1472,B_1473,C_1474) = k1_relat_1(C_1474)
      | ~ m1_subset_1(C_1474,k1_zfmisc_1(k2_zfmisc_1(A_1472,B_1473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7429,plain,(
    ! [A_1472,B_1473] : k1_relset_1(A_1472,B_1473,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_7405])).

tff(c_8020,plain,(
    ! [C_1547,B_1548] :
      ( v1_funct_2(C_1547,k1_xboole_0,B_1548)
      | k1_relset_1(k1_xboole_0,B_1548,C_1547) != k1_xboole_0
      | ~ m1_subset_1(C_1547,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_8026,plain,(
    ! [B_1548] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1548)
      | k1_relset_1(k1_xboole_0,B_1548,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_8020])).

tff(c_8029,plain,(
    ! [B_1548] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1548)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7429,c_8026])).

tff(c_8030,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8029])).

tff(c_6664,plain,(
    ! [C_1401] :
      ( v1_partfun1(C_1401,k1_xboole_0)
      | ~ m1_subset_1(C_1401,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6644])).

tff(c_7443,plain,(
    ! [C_1478] :
      ( v1_partfun1(C_1478,k1_xboole_0)
      | ~ m1_subset_1(C_1478,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6664])).

tff(c_7453,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_7443])).

tff(c_8155,plain,(
    ! [B_1557,C_1558] :
      ( k1_relset_1(k1_xboole_0,B_1557,C_1558) = k1_xboole_0
      | ~ v1_funct_2(C_1558,k1_xboole_0,B_1557)
      | ~ m1_subset_1(C_1558,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_8158,plain,(
    ! [B_1538] :
      ( k1_relset_1(k1_xboole_0,B_1538,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7985,c_8155])).

tff(c_8164,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7453,c_12,c_7429,c_8158])).

tff(c_8166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8030,c_8164])).

tff(c_8168,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8029])).

tff(c_8169,plain,(
    ! [A_1472,B_1473] : k1_relset_1(A_1472,B_1473,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8168,c_7429])).

tff(c_8199,plain,(
    ! [B_1562,A_1563,C_1564] :
      ( k1_xboole_0 = B_1562
      | k1_relset_1(A_1563,B_1562,C_1564) = A_1563
      | ~ v1_funct_2(C_1564,A_1563,B_1562)
      | ~ m1_subset_1(C_1564,k1_zfmisc_1(k2_zfmisc_1(A_1563,B_1562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8222,plain,(
    ! [B_1562,A_1563] :
      ( k1_xboole_0 = B_1562
      | k1_relset_1(A_1563,B_1562,k1_xboole_0) = A_1563
      | ~ v1_funct_2(k1_xboole_0,A_1563,B_1562) ) ),
    inference(resolution,[status(thm)],[c_12,c_8199])).

tff(c_8294,plain,(
    ! [B_1567,A_1568] :
      ( k1_xboole_0 = B_1567
      | k1_xboole_0 = A_1568
      | ~ v1_funct_2(k1_xboole_0,A_1568,B_1567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8169,c_8222])).

tff(c_8310,plain,(
    ! [B_1538,A_1537] :
      ( k1_xboole_0 = B_1538
      | k1_xboole_0 = A_1537
      | ~ v1_partfun1(k1_xboole_0,A_1537) ) ),
    inference(resolution,[status(thm)],[c_7985,c_8294])).

tff(c_8317,plain,(
    ! [A_1569] :
      ( k1_xboole_0 = A_1569
      | ~ v1_partfun1(k1_xboole_0,A_1569) ) ),
    inference(splitLeft,[status(thm)],[c_8310])).

tff(c_8377,plain,(
    ! [A_1573] :
      ( k1_xboole_0 = A_1573
      | ~ v1_xboole_0(A_1573) ) ),
    inference(resolution,[status(thm)],[c_6668,c_8317])).

tff(c_8384,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7404,c_8377])).

tff(c_8425,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_2',B_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8384,c_8384,c_10])).

tff(c_8510,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8425,c_124])).

tff(c_8623,plain,(
    ! [A_1585] :
      ( A_1585 = '#skF_2'
      | ~ r1_tarski(A_1585,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8384,c_8384,c_4])).

tff(c_8635,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8510,c_8623])).

tff(c_7403,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_6667])).

tff(c_8661,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8635,c_7403])).

tff(c_8395,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8384,c_8384,c_8168])).

tff(c_8653,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8635,c_8635,c_8395])).

tff(c_7459,plain,(
    ! [A_1480,B_1481,C_1482] :
      ( k2_relset_1(A_1480,B_1481,C_1482) = k2_relat_1(C_1482)
      | ~ m1_subset_1(C_1482,k1_zfmisc_1(k2_zfmisc_1(A_1480,B_1481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7469,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_7459])).

tff(c_7483,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7469])).

tff(c_8423,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8384,c_8384,c_8])).

tff(c_6558,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6547,c_14])).

tff(c_8545,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8423,c_6558])).

tff(c_8634,plain,(
    k2_funct_1('#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8545,c_8623])).

tff(c_8677,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8635,c_8634])).

tff(c_8686,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8677,c_34])).

tff(c_8699,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_76,c_70,c_7483,c_8686])).

tff(c_8756,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8653,c_8699])).

tff(c_7953,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6547,c_7944])).

tff(c_7977,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_7953])).

tff(c_7978,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6546,c_7977])).

tff(c_8678,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8677,c_7978])).

tff(c_8757,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8756,c_8678])).

tff(c_8763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8661,c_8757])).

tff(c_9101,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8310])).

tff(c_9102,plain,(
    v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9101,c_2])).

tff(c_9134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7442,c_9102])).

tff(c_9135,plain,(
    v1_partfun1(k2_funct_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6665])).

tff(c_9391,plain,(
    ! [C_2488,A_2489,B_2490] :
      ( v1_funct_2(C_2488,A_2489,B_2490)
      | ~ v1_partfun1(C_2488,A_2489)
      | ~ v1_funct_1(C_2488)
      | ~ m1_subset_1(C_2488,k1_zfmisc_1(k2_zfmisc_1(A_2489,B_2490))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9400,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6547,c_9391])).

tff(c_9424,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_9135,c_9400])).

tff(c_9426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6546,c_9424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.36/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.54  
% 7.36/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.54  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.36/2.54  
% 7.36/2.54  %Foreground sorts:
% 7.36/2.54  
% 7.36/2.54  
% 7.36/2.54  %Background operators:
% 7.36/2.54  
% 7.36/2.54  
% 7.36/2.54  %Foreground operators:
% 7.36/2.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.36/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.36/2.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.36/2.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.36/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.36/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.36/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.36/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.36/2.54  tff('#skF_2', type, '#skF_2': $i).
% 7.36/2.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.36/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.36/2.54  tff('#skF_1', type, '#skF_1': $i).
% 7.36/2.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.36/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.36/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.36/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.36/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.36/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.36/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.36/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.36/2.54  
% 7.75/2.58  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.75/2.58  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.75/2.58  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.75/2.58  tff(f_110, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 7.75/2.58  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.75/2.58  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.75/2.58  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.75/2.58  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.75/2.58  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.75/2.58  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.75/2.58  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.75/2.58  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.75/2.58  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.75/2.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.75/2.58  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 7.75/2.58  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.75/2.58  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.58  tff(c_113, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.75/2.58  tff(c_125, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(resolution, [status(thm)], [c_12, c_113])).
% 7.75/2.58  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_325, plain, (![C_81, A_82, B_83]: (v1_partfun1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.75/2.58  tff(c_344, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_325])).
% 7.75/2.58  tff(c_348, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_344])).
% 7.75/2.58  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_470, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.75/2.58  tff(c_493, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_470])).
% 7.75/2.58  tff(c_2209, plain, (![B_251, A_252, C_253]: (k1_xboole_0=B_251 | k1_relset_1(A_252, B_251, C_253)=A_252 | ~v1_funct_2(C_253, A_252, B_251) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_2222, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_2209])).
% 7.75/2.58  tff(c_2240, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_493, c_2222])).
% 7.75/2.58  tff(c_2244, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_2240])).
% 7.75/2.58  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_134, plain, (![A_46]: (v1_funct_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.75/2.58  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_133, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 7.75/2.58  tff(c_137, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_133])).
% 7.75/2.58  tff(c_140, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_137])).
% 7.75/2.58  tff(c_152, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.75/2.58  tff(c_159, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_152])).
% 7.75/2.58  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_159])).
% 7.75/2.58  tff(c_173, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 7.75/2.58  tff(c_254, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_173])).
% 7.75/2.58  tff(c_187, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.75/2.58  tff(c_204, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_187])).
% 7.75/2.58  tff(c_70, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_68, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.75/2.58  tff(c_516, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.75/2.58  tff(c_526, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_516])).
% 7.75/2.58  tff(c_540, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_526])).
% 7.75/2.58  tff(c_34, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.75/2.58  tff(c_24, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.75/2.58  tff(c_174, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 7.75/2.58  tff(c_361, plain, (![A_86]: (k1_relat_1(k2_funct_1(A_86))=k2_relat_1(A_86) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.75/2.58  tff(c_62, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.75/2.58  tff(c_1430, plain, (![A_201]: (v1_funct_2(k2_funct_1(A_201), k2_relat_1(A_201), k2_relat_1(k2_funct_1(A_201))) | ~v1_funct_1(k2_funct_1(A_201)) | ~v1_relat_1(k2_funct_1(A_201)) | ~v2_funct_1(A_201) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(superposition, [status(thm), theory('equality')], [c_361, c_62])).
% 7.75/2.58  tff(c_1433, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_540, c_1430])).
% 7.75/2.58  tff(c_1441, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_174, c_1433])).
% 7.75/2.58  tff(c_1442, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1441])).
% 7.75/2.58  tff(c_1445, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1442])).
% 7.75/2.58  tff(c_1449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_1445])).
% 7.75/2.58  tff(c_1451, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1441])).
% 7.75/2.58  tff(c_881, plain, (![B_154, A_155, C_156]: (k1_xboole_0=B_154 | k1_relset_1(A_155, B_154, C_156)=A_155 | ~v1_funct_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_894, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_881])).
% 7.75/2.58  tff(c_912, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_493, c_894])).
% 7.75/2.58  tff(c_916, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_912])).
% 7.75/2.58  tff(c_32, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.75/2.58  tff(c_414, plain, (![A_96]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96)))) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.75/2.58  tff(c_1533, plain, (![A_208]: (m1_subset_1(k2_funct_1(A_208), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_208)), k1_relat_1(A_208)))) | ~v1_funct_1(k2_funct_1(A_208)) | ~v1_relat_1(k2_funct_1(A_208)) | ~v2_funct_1(A_208) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_32, c_414])).
% 7.75/2.58  tff(c_1565, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_916, c_1533])).
% 7.75/2.58  tff(c_1586, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_1451, c_174, c_1565])).
% 7.75/2.58  tff(c_1620, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1586])).
% 7.75/2.58  tff(c_1639, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_540, c_1620])).
% 7.75/2.58  tff(c_1641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_1639])).
% 7.75/2.58  tff(c_1642, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_912])).
% 7.75/2.58  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.75/2.58  tff(c_1675, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1642, c_8])).
% 7.75/2.58  tff(c_124, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_113])).
% 7.75/2.58  tff(c_1752, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_124])).
% 7.75/2.58  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.75/2.58  tff(c_1902, plain, (![A_217]: (A_217='#skF_3' | ~r1_tarski(A_217, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1642, c_4])).
% 7.75/2.58  tff(c_1910, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1752, c_1902])).
% 7.75/2.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.75/2.58  tff(c_1678, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_2])).
% 7.75/2.58  tff(c_1927, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1678])).
% 7.75/2.58  tff(c_494, plain, (![A_101, B_102]: (k1_relset_1(A_101, B_102, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_470])).
% 7.75/2.58  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.75/2.58  tff(c_52, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_613, plain, (![C_113, B_114]: (v1_funct_2(C_113, k1_xboole_0, B_114) | k1_relset_1(k1_xboole_0, B_114, C_113)!=k1_xboole_0 | ~m1_subset_1(C_113, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 7.75/2.58  tff(c_619, plain, (![B_114]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_114) | k1_relset_1(k1_xboole_0, B_114, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_613])).
% 7.75/2.58  tff(c_622, plain, (![B_114]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_114) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_494, c_619])).
% 7.75/2.58  tff(c_627, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_622])).
% 7.75/2.58  tff(c_342, plain, (![C_81]: (v1_partfun1(C_81, k1_xboole_0) | ~m1_subset_1(C_81, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_325])).
% 7.75/2.58  tff(c_350, plain, (![C_85]: (v1_partfun1(C_85, k1_xboole_0) | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_342])).
% 7.75/2.58  tff(c_360, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_350])).
% 7.75/2.58  tff(c_260, plain, (![B_73, A_74]: (v1_funct_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.75/2.58  tff(c_273, plain, (![A_4]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_12, c_260])).
% 7.75/2.58  tff(c_298, plain, (![A_78]: (~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(splitLeft, [status(thm)], [c_273])).
% 7.75/2.58  tff(c_304, plain, (~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_204, c_298])).
% 7.75/2.58  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_304])).
% 7.75/2.58  tff(c_313, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_273])).
% 7.75/2.58  tff(c_675, plain, (![C_126, A_127, B_128]: (v1_funct_2(C_126, A_127, B_128) | ~v1_partfun1(C_126, A_127) | ~v1_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.75/2.58  tff(c_695, plain, (![A_127, B_128]: (v1_funct_2(k1_xboole_0, A_127, B_128) | ~v1_partfun1(k1_xboole_0, A_127) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_675])).
% 7.75/2.58  tff(c_710, plain, (![A_129, B_130]: (v1_funct_2(k1_xboole_0, A_129, B_130) | ~v1_partfun1(k1_xboole_0, A_129))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_695])).
% 7.75/2.58  tff(c_56, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_79, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 7.75/2.58  tff(c_713, plain, (![B_130]: (k1_relset_1(k1_xboole_0, B_130, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_710, c_79])).
% 7.75/2.58  tff(c_719, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_360, c_12, c_494, c_713])).
% 7.75/2.58  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_627, c_719])).
% 7.75/2.58  tff(c_723, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_622])).
% 7.75/2.58  tff(c_1655, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1642, c_723])).
% 7.75/2.58  tff(c_1924, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1910, c_1655])).
% 7.75/2.58  tff(c_60, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.75/2.58  tff(c_548, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_540, c_60])).
% 7.75/2.58  tff(c_557, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_548])).
% 7.75/2.58  tff(c_46, plain, (![C_30, A_27, B_28]: (v1_partfun1(C_30, A_27) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.75/2.58  tff(c_605, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_557, c_46])).
% 7.75/2.58  tff(c_782, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_605])).
% 7.75/2.58  tff(c_1993, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1924, c_782])).
% 7.75/2.58  tff(c_1996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1993])).
% 7.75/2.58  tff(c_1998, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_605])).
% 7.75/2.58  tff(c_2247, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_1998])).
% 7.75/2.58  tff(c_2255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_2247])).
% 7.75/2.58  tff(c_2256, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2240])).
% 7.75/2.58  tff(c_2292, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_8])).
% 7.75/2.58  tff(c_2441, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_124])).
% 7.75/2.58  tff(c_2508, plain, (![A_261]: (A_261='#skF_3' | ~r1_tarski(A_261, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_4])).
% 7.75/2.58  tff(c_2516, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2441, c_2508])).
% 7.75/2.58  tff(c_2294, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_10])).
% 7.75/2.58  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.75/2.58  tff(c_258, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_254])).
% 7.75/2.58  tff(c_2395, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2294, c_258])).
% 7.75/2.58  tff(c_2526, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2395])).
% 7.75/2.58  tff(c_2540, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_540])).
% 7.75/2.58  tff(c_3480, plain, (![A_353]: (v1_funct_2(k2_funct_1(A_353), k2_relat_1(A_353), k2_relat_1(k2_funct_1(A_353))) | ~v1_funct_1(k2_funct_1(A_353)) | ~v1_relat_1(k2_funct_1(A_353)) | ~v2_funct_1(A_353) | ~v1_funct_1(A_353) | ~v1_relat_1(A_353))), inference(superposition, [status(thm), theory('equality')], [c_361, c_62])).
% 7.75/2.58  tff(c_3483, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2540, c_3480])).
% 7.75/2.58  tff(c_3491, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_174, c_3483])).
% 7.75/2.58  tff(c_3492, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3491])).
% 7.75/2.58  tff(c_3495, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_3492])).
% 7.75/2.58  tff(c_3499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_3495])).
% 7.75/2.58  tff(c_3501, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3491])).
% 7.75/2.58  tff(c_2525, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2516, c_2292])).
% 7.75/2.58  tff(c_2272, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_723])).
% 7.75/2.58  tff(c_2531, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_2516, c_2272])).
% 7.75/2.58  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.75/2.58  tff(c_444, plain, (![A_98]: (r1_tarski(A_98, k2_zfmisc_1(k1_relat_1(A_98), k2_relat_1(A_98))) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_414, c_14])).
% 7.75/2.58  tff(c_3573, plain, (![A_359]: (r1_tarski(k2_funct_1(A_359), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_359)), k1_relat_1(A_359))) | ~v1_funct_1(k2_funct_1(A_359)) | ~v1_relat_1(k2_funct_1(A_359)) | ~v2_funct_1(A_359) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(superposition, [status(thm), theory('equality')], [c_32, c_444])).
% 7.75/2.58  tff(c_3600, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2531, c_3573])).
% 7.75/2.58  tff(c_3616, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_3501, c_174, c_2525, c_3600])).
% 7.75/2.58  tff(c_3618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2526, c_3616])).
% 7.75/2.58  tff(c_3620, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_344])).
% 7.75/2.58  tff(c_3646, plain, (![C_364, A_365]: (v1_partfun1(C_364, A_365) | ~m1_subset_1(C_364, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(A_365))), inference(superposition, [status(thm), theory('equality')], [c_8, c_325])).
% 7.75/2.58  tff(c_3653, plain, (![A_5, A_365]: (v1_partfun1(A_5, A_365) | ~v1_xboole_0(A_365) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3646])).
% 7.75/2.58  tff(c_4524, plain, (![C_439, A_440, B_441]: (v1_funct_2(C_439, A_440, B_441) | ~v1_partfun1(C_439, A_440) | ~v1_funct_1(C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.75/2.58  tff(c_4544, plain, (![A_440, B_441]: (v1_funct_2(k1_xboole_0, A_440, B_441) | ~v1_partfun1(k1_xboole_0, A_440) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_4524])).
% 7.75/2.58  tff(c_4558, plain, (![A_440, B_441]: (v1_funct_2(k1_xboole_0, A_440, B_441) | ~v1_partfun1(k1_xboole_0, A_440))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_4544])).
% 7.75/2.58  tff(c_3622, plain, (![C_361]: (v1_partfun1(C_361, k1_xboole_0) | ~m1_subset_1(C_361, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_342])).
% 7.75/2.58  tff(c_3632, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_3622])).
% 7.75/2.58  tff(c_3744, plain, (![A_377, B_378, C_379]: (k1_relset_1(A_377, B_378, C_379)=k1_relat_1(C_379) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.75/2.58  tff(c_3768, plain, (![A_377, B_378]: (k1_relset_1(A_377, B_378, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_3744])).
% 7.75/2.58  tff(c_4559, plain, (![A_442, B_443]: (v1_funct_2(k1_xboole_0, A_442, B_443) | ~v1_partfun1(k1_xboole_0, A_442))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_4544])).
% 7.75/2.58  tff(c_4562, plain, (![B_443]: (k1_relset_1(k1_xboole_0, B_443, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_4559, c_79])).
% 7.75/2.58  tff(c_4568, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3632, c_12, c_3768, c_4562])).
% 7.75/2.58  tff(c_4573, plain, (![A_377, B_378]: (k1_relset_1(A_377, B_378, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_3768])).
% 7.75/2.58  tff(c_4657, plain, (![B_455, A_456, C_457]: (k1_xboole_0=B_455 | k1_relset_1(A_456, B_455, C_457)=A_456 | ~v1_funct_2(C_457, A_456, B_455) | ~m1_subset_1(C_457, k1_zfmisc_1(k2_zfmisc_1(A_456, B_455))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_4677, plain, (![B_455, A_456]: (k1_xboole_0=B_455 | k1_relset_1(A_456, B_455, k1_xboole_0)=A_456 | ~v1_funct_2(k1_xboole_0, A_456, B_455))), inference(resolution, [status(thm)], [c_12, c_4657])).
% 7.75/2.58  tff(c_4737, plain, (![B_458, A_459]: (k1_xboole_0=B_458 | k1_xboole_0=A_459 | ~v1_funct_2(k1_xboole_0, A_459, B_458))), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_4677])).
% 7.75/2.58  tff(c_4753, plain, (![B_441, A_440]: (k1_xboole_0=B_441 | k1_xboole_0=A_440 | ~v1_partfun1(k1_xboole_0, A_440))), inference(resolution, [status(thm)], [c_4558, c_4737])).
% 7.75/2.58  tff(c_4789, plain, (![A_463]: (k1_xboole_0=A_463 | ~v1_partfun1(k1_xboole_0, A_463))), inference(splitLeft, [status(thm)], [c_4753])).
% 7.75/2.58  tff(c_4797, plain, (![A_365]: (k1_xboole_0=A_365 | ~v1_xboole_0(A_365) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_3653, c_4789])).
% 7.75/2.58  tff(c_4821, plain, (![A_464]: (k1_xboole_0=A_464 | ~v1_xboole_0(A_464))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_4797])).
% 7.75/2.58  tff(c_4828, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3620, c_4821])).
% 7.75/2.58  tff(c_4865, plain, (![B_3]: (k2_zfmisc_1('#skF_2', B_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4828, c_4828, c_10])).
% 7.75/2.58  tff(c_5004, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4865, c_124])).
% 7.75/2.58  tff(c_5100, plain, (![A_477]: (A_477='#skF_2' | ~r1_tarski(A_477, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4828, c_4828, c_4])).
% 7.75/2.58  tff(c_5108, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_5004, c_5100])).
% 7.75/2.58  tff(c_4863, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4828, c_4828, c_8])).
% 7.75/2.58  tff(c_4976, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_254])).
% 7.75/2.58  tff(c_5114, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5108, c_4976])).
% 7.75/2.58  tff(c_4842, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4828, c_4828, c_4568])).
% 7.75/2.58  tff(c_5127, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5108, c_5108, c_4842])).
% 7.75/2.58  tff(c_3676, plain, (![A_371]: (k2_relat_1(k2_funct_1(A_371))=k1_relat_1(A_371) | ~v2_funct_1(A_371) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.75/2.58  tff(c_5855, plain, (![A_559]: (v1_funct_2(k2_funct_1(A_559), k1_relat_1(k2_funct_1(A_559)), k1_relat_1(A_559)) | ~v1_funct_1(k2_funct_1(A_559)) | ~v1_relat_1(k2_funct_1(A_559)) | ~v2_funct_1(A_559) | ~v1_funct_1(A_559) | ~v1_relat_1(A_559))), inference(superposition, [status(thm), theory('equality')], [c_3676, c_62])).
% 7.75/2.58  tff(c_5858, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5127, c_5855])).
% 7.75/2.58  tff(c_5866, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_174, c_5858])).
% 7.75/2.58  tff(c_5867, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5866])).
% 7.75/2.58  tff(c_5870, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_5867])).
% 7.75/2.58  tff(c_5874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_5870])).
% 7.75/2.58  tff(c_5876, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5866])).
% 7.75/2.58  tff(c_5121, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5108, c_5108, c_4863])).
% 7.75/2.58  tff(c_3695, plain, (![A_374]: (m1_subset_1(A_374, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_374), k2_relat_1(A_374)))) | ~v1_funct_1(A_374) | ~v1_relat_1(A_374))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.75/2.58  tff(c_6160, plain, (![A_586]: (m1_subset_1(k2_funct_1(A_586), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_586)), k1_relat_1(A_586)))) | ~v1_funct_1(k2_funct_1(A_586)) | ~v1_relat_1(k2_funct_1(A_586)) | ~v2_funct_1(A_586) | ~v1_funct_1(A_586) | ~v1_relat_1(A_586))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3695])).
% 7.75/2.58  tff(c_6192, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5127, c_6160])).
% 7.75/2.58  tff(c_6210, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_5876, c_174, c_5121, c_6192])).
% 7.75/2.58  tff(c_6212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5114, c_6210])).
% 7.75/2.58  tff(c_6214, plain, (![B_587]: (k1_xboole_0=B_587)), inference(splitRight, [status(thm)], [c_4753])).
% 7.75/2.58  tff(c_6437, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6214, c_258])).
% 7.75/2.58  tff(c_6545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_6437])).
% 7.75/2.58  tff(c_6546, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_173])).
% 7.75/2.58  tff(c_6547, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_173])).
% 7.75/2.58  tff(c_6644, plain, (![C_1401, A_1402, B_1403]: (v1_partfun1(C_1401, A_1402) | ~m1_subset_1(C_1401, k1_zfmisc_1(k2_zfmisc_1(A_1402, B_1403))) | ~v1_xboole_0(A_1402))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.75/2.58  tff(c_6665, plain, (v1_partfun1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6547, c_6644])).
% 7.75/2.58  tff(c_7442, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_6665])).
% 7.75/2.58  tff(c_6667, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_6644])).
% 7.75/2.58  tff(c_6671, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6667])).
% 7.75/2.58  tff(c_6736, plain, (![A_1416, B_1417, C_1418]: (k2_relset_1(A_1416, B_1417, C_1418)=k2_relat_1(C_1418) | ~m1_subset_1(C_1418, k1_zfmisc_1(k2_zfmisc_1(A_1416, B_1417))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.75/2.58  tff(c_6746, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_6736])).
% 7.75/2.58  tff(c_6760, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6746])).
% 7.75/2.58  tff(c_6674, plain, (![A_1405, B_1406, C_1407]: (k1_relset_1(A_1405, B_1406, C_1407)=k1_relat_1(C_1407) | ~m1_subset_1(C_1407, k1_zfmisc_1(k2_zfmisc_1(A_1405, B_1406))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.75/2.58  tff(c_6695, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6547, c_6674])).
% 7.75/2.58  tff(c_7317, plain, (![B_1469, C_1470, A_1471]: (k1_xboole_0=B_1469 | v1_funct_2(C_1470, A_1471, B_1469) | k1_relset_1(A_1471, B_1469, C_1470)!=A_1471 | ~m1_subset_1(C_1470, k1_zfmisc_1(k2_zfmisc_1(A_1471, B_1469))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_7326, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_6547, c_7317])).
% 7.75/2.58  tff(c_7349, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6695, c_7326])).
% 7.75/2.58  tff(c_7350, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6546, c_7349])).
% 7.75/2.58  tff(c_7357, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_7350])).
% 7.75/2.58  tff(c_7360, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_7357])).
% 7.75/2.58  tff(c_7363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_6760, c_7360])).
% 7.75/2.58  tff(c_7364, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7350])).
% 7.75/2.58  tff(c_7400, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_2])).
% 7.75/2.58  tff(c_7402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6671, c_7400])).
% 7.75/2.58  tff(c_7404, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_6667])).
% 7.75/2.58  tff(c_6668, plain, (![A_1402]: (v1_partfun1(k1_xboole_0, A_1402) | ~v1_xboole_0(A_1402))), inference(resolution, [status(thm)], [c_12, c_6644])).
% 7.75/2.58  tff(c_36, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.75/2.58  tff(c_6557, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6547, c_36])).
% 7.75/2.58  tff(c_6565, plain, (![B_1393, A_1394]: (v1_funct_1(B_1393) | ~m1_subset_1(B_1393, k1_zfmisc_1(A_1394)) | ~v1_funct_1(A_1394) | ~v1_relat_1(A_1394))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.75/2.58  tff(c_6583, plain, (![A_4]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_12, c_6565])).
% 7.75/2.58  tff(c_6585, plain, (![A_1395]: (~v1_funct_1(A_1395) | ~v1_relat_1(A_1395))), inference(splitLeft, [status(thm)], [c_6583])).
% 7.75/2.58  tff(c_6588, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6557, c_6585])).
% 7.75/2.58  tff(c_6601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_6588])).
% 7.75/2.58  tff(c_6602, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_6583])).
% 7.75/2.58  tff(c_7944, plain, (![C_1536, A_1537, B_1538]: (v1_funct_2(C_1536, A_1537, B_1538) | ~v1_partfun1(C_1536, A_1537) | ~v1_funct_1(C_1536) | ~m1_subset_1(C_1536, k1_zfmisc_1(k2_zfmisc_1(A_1537, B_1538))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.75/2.58  tff(c_7967, plain, (![A_1537, B_1538]: (v1_funct_2(k1_xboole_0, A_1537, B_1538) | ~v1_partfun1(k1_xboole_0, A_1537) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_7944])).
% 7.75/2.58  tff(c_7985, plain, (![A_1537, B_1538]: (v1_funct_2(k1_xboole_0, A_1537, B_1538) | ~v1_partfun1(k1_xboole_0, A_1537))), inference(demodulation, [status(thm), theory('equality')], [c_6602, c_7967])).
% 7.75/2.58  tff(c_7405, plain, (![A_1472, B_1473, C_1474]: (k1_relset_1(A_1472, B_1473, C_1474)=k1_relat_1(C_1474) | ~m1_subset_1(C_1474, k1_zfmisc_1(k2_zfmisc_1(A_1472, B_1473))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.75/2.58  tff(c_7429, plain, (![A_1472, B_1473]: (k1_relset_1(A_1472, B_1473, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_7405])).
% 7.75/2.58  tff(c_8020, plain, (![C_1547, B_1548]: (v1_funct_2(C_1547, k1_xboole_0, B_1548) | k1_relset_1(k1_xboole_0, B_1548, C_1547)!=k1_xboole_0 | ~m1_subset_1(C_1547, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 7.75/2.58  tff(c_8026, plain, (![B_1548]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1548) | k1_relset_1(k1_xboole_0, B_1548, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_8020])).
% 7.75/2.58  tff(c_8029, plain, (![B_1548]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1548) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7429, c_8026])).
% 7.75/2.58  tff(c_8030, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8029])).
% 7.75/2.58  tff(c_6664, plain, (![C_1401]: (v1_partfun1(C_1401, k1_xboole_0) | ~m1_subset_1(C_1401, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6644])).
% 7.75/2.58  tff(c_7443, plain, (![C_1478]: (v1_partfun1(C_1478, k1_xboole_0) | ~m1_subset_1(C_1478, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6664])).
% 7.75/2.58  tff(c_7453, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_7443])).
% 7.75/2.58  tff(c_8155, plain, (![B_1557, C_1558]: (k1_relset_1(k1_xboole_0, B_1557, C_1558)=k1_xboole_0 | ~v1_funct_2(C_1558, k1_xboole_0, B_1557) | ~m1_subset_1(C_1558, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 7.75/2.58  tff(c_8158, plain, (![B_1538]: (k1_relset_1(k1_xboole_0, B_1538, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_7985, c_8155])).
% 7.75/2.58  tff(c_8164, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7453, c_12, c_7429, c_8158])).
% 7.75/2.58  tff(c_8166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8030, c_8164])).
% 7.75/2.58  tff(c_8168, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8029])).
% 7.75/2.58  tff(c_8169, plain, (![A_1472, B_1473]: (k1_relset_1(A_1472, B_1473, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8168, c_7429])).
% 7.75/2.58  tff(c_8199, plain, (![B_1562, A_1563, C_1564]: (k1_xboole_0=B_1562 | k1_relset_1(A_1563, B_1562, C_1564)=A_1563 | ~v1_funct_2(C_1564, A_1563, B_1562) | ~m1_subset_1(C_1564, k1_zfmisc_1(k2_zfmisc_1(A_1563, B_1562))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.75/2.58  tff(c_8222, plain, (![B_1562, A_1563]: (k1_xboole_0=B_1562 | k1_relset_1(A_1563, B_1562, k1_xboole_0)=A_1563 | ~v1_funct_2(k1_xboole_0, A_1563, B_1562))), inference(resolution, [status(thm)], [c_12, c_8199])).
% 7.75/2.58  tff(c_8294, plain, (![B_1567, A_1568]: (k1_xboole_0=B_1567 | k1_xboole_0=A_1568 | ~v1_funct_2(k1_xboole_0, A_1568, B_1567))), inference(demodulation, [status(thm), theory('equality')], [c_8169, c_8222])).
% 7.75/2.58  tff(c_8310, plain, (![B_1538, A_1537]: (k1_xboole_0=B_1538 | k1_xboole_0=A_1537 | ~v1_partfun1(k1_xboole_0, A_1537))), inference(resolution, [status(thm)], [c_7985, c_8294])).
% 7.75/2.58  tff(c_8317, plain, (![A_1569]: (k1_xboole_0=A_1569 | ~v1_partfun1(k1_xboole_0, A_1569))), inference(splitLeft, [status(thm)], [c_8310])).
% 7.75/2.58  tff(c_8377, plain, (![A_1573]: (k1_xboole_0=A_1573 | ~v1_xboole_0(A_1573))), inference(resolution, [status(thm)], [c_6668, c_8317])).
% 7.75/2.58  tff(c_8384, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7404, c_8377])).
% 7.75/2.58  tff(c_8425, plain, (![B_3]: (k2_zfmisc_1('#skF_2', B_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8384, c_8384, c_10])).
% 7.75/2.58  tff(c_8510, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8425, c_124])).
% 7.75/2.58  tff(c_8623, plain, (![A_1585]: (A_1585='#skF_2' | ~r1_tarski(A_1585, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8384, c_8384, c_4])).
% 7.75/2.58  tff(c_8635, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_8510, c_8623])).
% 7.75/2.58  tff(c_7403, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_6667])).
% 7.75/2.58  tff(c_8661, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8635, c_7403])).
% 7.75/2.58  tff(c_8395, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8384, c_8384, c_8168])).
% 7.75/2.58  tff(c_8653, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8635, c_8635, c_8395])).
% 7.75/2.58  tff(c_7459, plain, (![A_1480, B_1481, C_1482]: (k2_relset_1(A_1480, B_1481, C_1482)=k2_relat_1(C_1482) | ~m1_subset_1(C_1482, k1_zfmisc_1(k2_zfmisc_1(A_1480, B_1481))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.75/2.58  tff(c_7469, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_7459])).
% 7.75/2.58  tff(c_7483, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7469])).
% 7.75/2.58  tff(c_8423, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8384, c_8384, c_8])).
% 7.75/2.58  tff(c_6558, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_6547, c_14])).
% 7.75/2.58  tff(c_8545, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8423, c_6558])).
% 7.75/2.58  tff(c_8634, plain, (k2_funct_1('#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_8545, c_8623])).
% 7.75/2.58  tff(c_8677, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8635, c_8634])).
% 7.75/2.58  tff(c_8686, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8677, c_34])).
% 7.75/2.58  tff(c_8699, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_76, c_70, c_7483, c_8686])).
% 7.75/2.58  tff(c_8756, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8653, c_8699])).
% 7.75/2.58  tff(c_7953, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_partfun1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6547, c_7944])).
% 7.75/2.58  tff(c_7977, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_partfun1(k2_funct_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_7953])).
% 7.75/2.58  tff(c_7978, plain, (~v1_partfun1(k2_funct_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_6546, c_7977])).
% 7.75/2.58  tff(c_8678, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8677, c_7978])).
% 7.75/2.58  tff(c_8757, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8756, c_8678])).
% 7.75/2.58  tff(c_8763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8661, c_8757])).
% 7.75/2.58  tff(c_9101, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_8310])).
% 7.75/2.58  tff(c_9102, plain, (v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9101, c_2])).
% 7.75/2.58  tff(c_9134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7442, c_9102])).
% 7.75/2.58  tff(c_9135, plain, (v1_partfun1(k2_funct_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_6665])).
% 7.75/2.58  tff(c_9391, plain, (![C_2488, A_2489, B_2490]: (v1_funct_2(C_2488, A_2489, B_2490) | ~v1_partfun1(C_2488, A_2489) | ~v1_funct_1(C_2488) | ~m1_subset_1(C_2488, k1_zfmisc_1(k2_zfmisc_1(A_2489, B_2490))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.75/2.58  tff(c_9400, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_partfun1(k2_funct_1('#skF_4'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6547, c_9391])).
% 7.75/2.58  tff(c_9424, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_9135, c_9400])).
% 7.75/2.58  tff(c_9426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6546, c_9424])).
% 7.75/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/2.58  
% 7.75/2.58  Inference rules
% 7.75/2.58  ----------------------
% 7.75/2.58  #Ref     : 0
% 7.75/2.58  #Sup     : 1956
% 7.75/2.58  #Fact    : 0
% 7.75/2.58  #Define  : 0
% 7.75/2.58  #Split   : 35
% 7.75/2.58  #Chain   : 0
% 7.75/2.58  #Close   : 0
% 7.75/2.58  
% 7.75/2.58  Ordering : KBO
% 7.75/2.58  
% 7.75/2.58  Simplification rules
% 7.75/2.58  ----------------------
% 7.75/2.58  #Subsume      : 393
% 7.75/2.58  #Demod        : 2475
% 7.75/2.58  #Tautology    : 917
% 7.75/2.58  #SimpNegUnit  : 23
% 7.75/2.58  #BackRed      : 494
% 7.75/2.58  
% 7.75/2.58  #Partial instantiations: 544
% 7.75/2.58  #Strategies tried      : 1
% 7.75/2.58  
% 7.75/2.58  Timing (in seconds)
% 7.75/2.58  ----------------------
% 7.75/2.58  Preprocessing        : 0.34
% 7.75/2.58  Parsing              : 0.18
% 7.75/2.58  CNF conversion       : 0.02
% 7.75/2.58  Main loop            : 1.42
% 7.75/2.58  Inferencing          : 0.52
% 7.75/2.58  Reduction            : 0.48
% 7.75/2.58  Demodulation         : 0.34
% 7.75/2.58  BG Simplification    : 0.05
% 7.75/2.58  Subsumption          : 0.23
% 7.75/2.58  Abstraction          : 0.06
% 7.75/2.58  MUC search           : 0.00
% 7.75/2.58  Cooper               : 0.00
% 7.75/2.58  Total                : 1.85
% 7.75/2.58  Index Insertion      : 0.00
% 7.75/2.58  Index Deletion       : 0.00
% 7.75/2.58  Index Matching       : 0.00
% 7.75/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
