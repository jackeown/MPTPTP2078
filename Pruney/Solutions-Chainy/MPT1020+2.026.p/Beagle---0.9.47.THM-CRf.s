%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :  243 (5248 expanded)
%              Number of leaves         :   46 (1701 expanded)
%              Depth                    :   20
%              Number of atoms          :  519 (13191 expanded)
%              Number of equality atoms :  185 (4860 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_186,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_338,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_relset_1(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_349,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_338])).

tff(c_52,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_12,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_4] : k1_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_1] : v1_relat_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_112,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) != k1_xboole_0
      | k1_xboole_0 = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_1] :
      ( k1_relat_1(k6_partfun1(A_1)) != k1_xboole_0
      | k6_partfun1(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_82,c_112])).

tff(c_117,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | k6_partfun1(A_1) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_115])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_153,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_62])).

tff(c_272,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_78,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_76,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_210,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_223,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_280,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_292,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_280])).

tff(c_365,plain,(
    ! [B_90,A_91] :
      ( k2_relat_1(B_90) = A_91
      | ~ v2_funct_2(B_90,A_91)
      | ~ v5_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_374,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_292,c_365])).

tff(c_386,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_374])).

tff(c_390,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_74,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_593,plain,(
    ! [C_114,B_115,A_116] :
      ( v2_funct_2(C_114,B_115)
      | ~ v3_funct_2(C_114,A_116,B_115)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_605,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_593])).

tff(c_614,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_605])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_614])).

tff(c_617,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_734,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_746,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_734])).

tff(c_754,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_746])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_348,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_338])).

tff(c_755,plain,(
    ! [C_132,A_133,B_134] :
      ( v2_funct_1(C_132)
      | ~ v3_funct_2(C_132,A_133,B_134)
      | ~ v1_funct_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_767,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_755])).

tff(c_775,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_767])).

tff(c_1058,plain,(
    ! [C_171,D_173,B_174,E_170,A_169,F_172] :
      ( k1_partfun1(A_169,B_174,C_171,D_173,E_170,F_172) = k5_relat_1(E_170,F_172)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_171,D_173)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_174)))
      | ~ v1_funct_1(E_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1064,plain,(
    ! [A_169,B_174,E_170] :
      ( k1_partfun1(A_169,B_174,'#skF_1','#skF_1',E_170,'#skF_3') = k5_relat_1(E_170,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_169,B_174)))
      | ~ v1_funct_1(E_170) ) ),
    inference(resolution,[status(thm)],[c_64,c_1058])).

tff(c_1082,plain,(
    ! [A_177,B_178,E_179] :
      ( k1_partfun1(A_177,B_178,'#skF_1','#skF_1',E_179,'#skF_3') = k5_relat_1(E_179,'#skF_3')
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_1(E_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1064])).

tff(c_1094,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1082])).

tff(c_1102,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1094])).

tff(c_851,plain,(
    ! [D_143,C_144,A_145,B_146] :
      ( D_143 = C_144
      | ~ r2_relset_1(A_145,B_146,C_144,D_143)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_865,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_851])).

tff(c_888,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_865])).

tff(c_889,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_1109,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_889])).

tff(c_1123,plain,(
    ! [E_185,A_182,C_184,F_183,D_180,B_181] :
      ( m1_subset_1(k1_partfun1(A_182,B_181,C_184,D_180,E_185,F_183),k1_zfmisc_1(k2_zfmisc_1(A_182,D_180)))
      | ~ m1_subset_1(F_183,k1_zfmisc_1(k2_zfmisc_1(C_184,D_180)))
      | ~ v1_funct_1(F_183)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181)))
      | ~ v1_funct_1(E_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1163,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_1123])).

tff(c_1181,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_64,c_1163])).

tff(c_1183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1109,c_1181])).

tff(c_1184,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_2079,plain,(
    ! [C_240,D_241,B_242,A_243] :
      ( k2_funct_1(C_240) = D_241
      | k1_xboole_0 = B_242
      | k1_xboole_0 = A_243
      | ~ v2_funct_1(C_240)
      | ~ r2_relset_1(A_243,A_243,k1_partfun1(A_243,B_242,B_242,A_243,C_240,D_241),k6_partfun1(A_243))
      | k2_relset_1(A_243,B_242,C_240) != B_242
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(B_242,A_243)))
      | ~ v1_funct_2(D_241,B_242,A_243)
      | ~ v1_funct_1(D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242)))
      | ~ v1_funct_2(C_240,A_243,B_242)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2094,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_2079])).

tff(c_2111,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_64,c_754,c_348,c_775,c_2094])).

tff(c_2112,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_2111])).

tff(c_1193,plain,(
    ! [A_186,B_187] :
      ( k2_funct_2(A_186,B_187) = k2_funct_1(B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1205,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1193])).

tff(c_1213,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1205])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1218,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_60])).

tff(c_2115,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2112,c_1218])).

tff(c_2119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_2115])).

tff(c_2121,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_222,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_210])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_222,c_4])).

tff(c_257,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_2123,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_257])).

tff(c_2141,plain,(
    ! [C_245,B_246,A_247] :
      ( v5_relat_1(C_245,B_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2152,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2141])).

tff(c_2233,plain,(
    ! [B_258,A_259] :
      ( k2_relat_1(B_258) = A_259
      | ~ v2_funct_2(B_258,A_259)
      | ~ v5_relat_1(B_258,A_259)
      | ~ v1_relat_1(B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2245,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2152,c_2233])).

tff(c_2258,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2245])).

tff(c_2259,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2123,c_2258])).

tff(c_66,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_2473,plain,(
    ! [C_279,B_280,A_281] :
      ( v2_funct_2(C_279,B_280)
      | ~ v3_funct_2(C_279,A_281,B_280)
      | ~ v1_funct_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2482,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2473])).

tff(c_2491,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2482])).

tff(c_2493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2259,c_2491])).

tff(c_2494,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_120,plain,(
    ! [A_60] :
      ( k1_xboole_0 != A_60
      | k6_partfun1(A_60) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_115])).

tff(c_132,plain,(
    ! [A_60] :
      ( k1_relat_1(k1_xboole_0) = A_60
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_81])).

tff(c_2554,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2494,c_132])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_239,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_222,c_6])).

tff(c_256,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_2496,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_256])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2554,c_2496])).

tff(c_2558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_2601,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_153])).

tff(c_2602,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2601])).

tff(c_14,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [A_4] : k2_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_135,plain,(
    ! [A_60] :
      ( k2_relat_1(k1_xboole_0) = A_60
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_80])).

tff(c_2579,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_135])).

tff(c_2640,plain,(
    ! [C_298,B_299,A_300] :
      ( v5_relat_1(C_298,B_299)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_300,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2651,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_2640])).

tff(c_2743,plain,(
    ! [B_310,A_311] :
      ( k2_relat_1(B_310) = A_311
      | ~ v2_funct_2(B_310,A_311)
      | ~ v5_relat_1(B_310,A_311)
      | ~ v1_relat_1(B_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2755,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2651,c_2743])).

tff(c_2767,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_2579,c_2755])).

tff(c_2768,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2602,c_2767])).

tff(c_2932,plain,(
    ! [C_328,B_329,A_330] :
      ( v2_funct_2(C_328,B_329)
      | ~ v3_funct_2(C_328,A_330,B_329)
      | ~ v1_funct_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2941,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2932])).

tff(c_2952,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2941])).

tff(c_2954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2768,c_2952])).

tff(c_2956,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2601])).

tff(c_2961,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_2558])).

tff(c_126,plain,(
    ! [A_60] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_60,A_60)))
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_46])).

tff(c_3478,plain,(
    ! [A_60] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_60,A_60)))
      | A_60 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2961,c_2961,c_126])).

tff(c_3535,plain,(
    ! [A_387,B_388,D_389] :
      ( r2_relset_1(A_387,B_388,D_389,D_389)
      | ~ m1_subset_1(D_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3549,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3478,c_3535])).

tff(c_2968,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_70])).

tff(c_254,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_223,c_4])).

tff(c_2981,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2961,c_2961,c_254])).

tff(c_2982,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2981])).

tff(c_2983,plain,(
    ! [C_331,B_332,A_333] :
      ( v5_relat_1(C_331,B_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2991,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2983])).

tff(c_3077,plain,(
    ! [B_343,A_344] :
      ( k2_relat_1(B_343) = A_344
      | ~ v2_funct_2(B_343,A_344)
      | ~ v5_relat_1(B_343,A_344)
      | ~ v1_relat_1(B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3086,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2991,c_3077])).

tff(c_3095,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_3086])).

tff(c_3096,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2982,c_3095])).

tff(c_3305,plain,(
    ! [C_366,B_367,A_368] :
      ( v2_funct_2(C_366,B_367)
      | ~ v3_funct_2(C_366,A_368,B_367)
      | ~ v1_funct_1(C_366)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_368,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3314,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_3305])).

tff(c_3322,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_3314])).

tff(c_3324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3096,c_3322])).

tff(c_3325,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2981])).

tff(c_3326,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2981])).

tff(c_3342,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_3326])).

tff(c_2962,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_222])).

tff(c_3611,plain,(
    ! [C_400,A_401,B_402] :
      ( v2_funct_1(C_400)
      | ~ v3_funct_2(C_400,A_401,B_402)
      | ~ v1_funct_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3614,plain,(
    ! [A_60] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_60,A_60)
      | ~ v1_funct_1('#skF_1')
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_3611])).

tff(c_3620,plain,(
    ! [A_60] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_60,A_60)
      | A_60 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3614])).

tff(c_3623,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3620])).

tff(c_2967,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_66])).

tff(c_3625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3623,c_2967])).

tff(c_3626,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3620])).

tff(c_2559,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_2574,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2559])).

tff(c_2960,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_2956,c_2574])).

tff(c_2567,plain,(
    ! [A_1] :
      ( A_1 != '#skF_3'
      | k6_partfun1(A_1) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_117])).

tff(c_3362,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_2956,c_2567])).

tff(c_16,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4603,plain,(
    ! [A_535,B_536] :
      ( k2_funct_1(A_535) = B_536
      | k6_partfun1(k2_relat_1(A_535)) != k5_relat_1(B_536,A_535)
      | k2_relat_1(B_536) != k1_relat_1(A_535)
      | ~ v2_funct_1(A_535)
      | ~ v1_funct_1(B_536)
      | ~ v1_relat_1(B_536)
      | ~ v1_funct_1(A_535)
      | ~ v1_relat_1(A_535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_4608,plain,(
    ! [B_536] :
      ( k2_funct_1('#skF_1') = B_536
      | k5_relat_1(B_536,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_536) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_536)
      | ~ v1_relat_1(B_536)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3342,c_4603])).

tff(c_4615,plain,(
    ! [B_537] :
      ( k2_funct_1('#skF_1') = B_537
      | k5_relat_1(B_537,'#skF_1') != '#skF_1'
      | k2_relat_1(B_537) != '#skF_1'
      | ~ v1_funct_1(B_537)
      | ~ v1_relat_1(B_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2962,c_2968,c_3626,c_2960,c_3362,c_4608])).

tff(c_4618,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2962,c_4615])).

tff(c_4624,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3342,c_4618])).

tff(c_4627,plain,(
    k5_relat_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4624])).

tff(c_4702,plain,(
    ! [B_563,F_561,E_559,A_558,D_562,C_560] :
      ( k1_partfun1(A_558,B_563,C_560,D_562,E_559,F_561) = k5_relat_1(E_559,F_561)
      | ~ m1_subset_1(F_561,k1_zfmisc_1(k2_zfmisc_1(C_560,D_562)))
      | ~ v1_funct_1(F_561)
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(A_558,B_563)))
      | ~ v1_funct_1(E_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4704,plain,(
    ! [A_558,B_563,A_60,E_559] :
      ( k1_partfun1(A_558,B_563,A_60,A_60,E_559,'#skF_1') = k5_relat_1(E_559,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(A_558,B_563)))
      | ~ v1_funct_1(E_559)
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_4702])).

tff(c_4733,plain,(
    ! [A_572,B_573,A_574,E_575] :
      ( k1_partfun1(A_572,B_573,A_574,A_574,E_575,'#skF_1') = k5_relat_1(E_575,'#skF_1')
      | ~ m1_subset_1(E_575,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573)))
      | ~ v1_funct_1(E_575)
      | A_574 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_4704])).

tff(c_4735,plain,(
    ! [A_60,A_574] :
      ( k1_partfun1(A_60,A_60,A_574,A_574,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_574 != '#skF_1'
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_4733])).

tff(c_4743,plain,(
    ! [A_576,A_577] :
      ( k1_partfun1(A_576,A_576,A_577,A_577,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | A_577 != '#skF_1'
      | A_576 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_4735])).

tff(c_3361,plain,(
    ! [A_1] :
      ( A_1 != '#skF_1'
      | k6_partfun1(A_1) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_2956,c_2567])).

tff(c_3799,plain,(
    ! [F_442,C_441,D_443,B_444,E_440,A_439] :
      ( k1_partfun1(A_439,B_444,C_441,D_443,E_440,F_442) = k5_relat_1(E_440,F_442)
      | ~ m1_subset_1(F_442,k1_zfmisc_1(k2_zfmisc_1(C_441,D_443)))
      | ~ v1_funct_1(F_442)
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(A_439,B_444)))
      | ~ v1_funct_1(E_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3801,plain,(
    ! [A_439,B_444,A_60,E_440] :
      ( k1_partfun1(A_439,B_444,A_60,A_60,E_440,'#skF_1') = k5_relat_1(E_440,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_440,k1_zfmisc_1(k2_zfmisc_1(A_439,B_444)))
      | ~ v1_funct_1(E_440)
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_3799])).

tff(c_3830,plain,(
    ! [A_453,B_454,A_455,E_456] :
      ( k1_partfun1(A_453,B_454,A_455,A_455,E_456,'#skF_1') = k5_relat_1(E_456,'#skF_1')
      | ~ m1_subset_1(E_456,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | ~ v1_funct_1(E_456)
      | A_455 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3801])).

tff(c_3950,plain,(
    ! [A_473,A_474] :
      ( k1_partfun1(A_473,A_473,A_474,A_474,k6_partfun1(A_473),'#skF_1') = k5_relat_1(k6_partfun1(A_473),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_473))
      | A_474 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_46,c_3830])).

tff(c_3952,plain,(
    ! [A_1,A_474] :
      ( k1_partfun1(A_1,A_1,A_474,A_474,k6_partfun1(A_1),'#skF_1') = k5_relat_1(k6_partfun1(A_1),'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_474 != '#skF_1'
      | A_1 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3361,c_3950])).

tff(c_3956,plain,(
    ! [A_475,A_476] :
      ( k1_partfun1(A_475,A_475,A_476,A_476,k6_partfun1(A_475),'#skF_1') = k5_relat_1(k6_partfun1(A_475),'#skF_1')
      | A_476 != '#skF_1'
      | A_475 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3952])).

tff(c_40,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3970,plain,(
    ! [A_475,A_476] :
      ( m1_subset_1(k5_relat_1(k6_partfun1(A_475),'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(A_475,A_476)))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_476,A_476)))
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(k6_partfun1(A_475),k1_zfmisc_1(k2_zfmisc_1(A_475,A_475)))
      | ~ v1_funct_1(k6_partfun1(A_475))
      | A_476 != '#skF_1'
      | A_475 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3956,c_40])).

tff(c_4172,plain,(
    ! [A_494,A_495] :
      ( m1_subset_1(k5_relat_1(k6_partfun1(A_494),'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(A_494,A_495)))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_495,A_495)))
      | ~ v1_funct_1(k6_partfun1(A_494))
      | A_495 != '#skF_1'
      | A_494 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2968,c_3970])).

tff(c_4177,plain,(
    ! [A_496,A_497] :
      ( m1_subset_1(k5_relat_1(k6_partfun1(A_496),'#skF_1'),k1_zfmisc_1(k2_zfmisc_1(A_496,A_497)))
      | ~ v1_funct_1(k6_partfun1(A_496))
      | A_496 != '#skF_1'
      | A_497 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_4172])).

tff(c_4514,plain,(
    ! [A_529,A_530] :
      ( m1_subset_1(k5_relat_1('#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(A_529,A_530)))
      | ~ v1_funct_1(k6_partfun1(A_529))
      | A_529 != '#skF_1'
      | A_530 != '#skF_1'
      | A_529 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3361,c_4177])).

tff(c_3832,plain,(
    ! [A_60,A_455] :
      ( k1_partfun1(A_60,A_60,A_455,A_455,'#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_455 != '#skF_1'
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_3830])).

tff(c_3839,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3832])).

tff(c_3479,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2961,c_2961,c_126])).

tff(c_2963,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_62])).

tff(c_3534,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_3325,c_2963])).

tff(c_3650,plain,(
    ! [D_408,C_409,A_410,B_411] :
      ( D_408 = C_409
      | ~ r2_relset_1(A_410,B_411,C_409,D_408)
      | ~ m1_subset_1(D_408,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411)))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3660,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3534,c_3650])).

tff(c_3675,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3479,c_3660])).

tff(c_3676,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3675])).

tff(c_3840,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3839,c_3676])).

tff(c_4521,plain,(
    ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4514,c_3840])).

tff(c_4565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_3362,c_4521])).

tff(c_4566,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3675])).

tff(c_4752,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4743,c_4566])).

tff(c_4763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4627,c_4752])).

tff(c_4764,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4624])).

tff(c_2966,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_68])).

tff(c_4575,plain,(
    ! [A_531,B_532] :
      ( k2_funct_2(A_531,B_532) = k2_funct_1(B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(k2_zfmisc_1(A_531,A_531)))
      | ~ v3_funct_2(B_532,A_531,A_531)
      | ~ v1_funct_2(B_532,A_531,A_531)
      | ~ v1_funct_1(B_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4578,plain,(
    ! [A_60] :
      ( k2_funct_2(A_60,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_60,A_60)
      | ~ v1_funct_2('#skF_1',A_60,A_60)
      | ~ v1_funct_1('#skF_1')
      | A_60 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3478,c_4575])).

tff(c_4587,plain,(
    ! [A_533] :
      ( k2_funct_2(A_533,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_533,A_533)
      | ~ v1_funct_2('#skF_1',A_533,A_533)
      | A_533 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_4578])).

tff(c_4590,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2967,c_4587])).

tff(c_4593,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2966,c_4590])).

tff(c_2964,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_60])).

tff(c_3444,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3325,c_2964])).

tff(c_4594,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4593,c_3444])).

tff(c_4776,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4764,c_4594])).

tff(c_4781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_4776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.28  
% 6.36/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.29  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.36/2.29  
% 6.36/2.29  %Foreground sorts:
% 6.36/2.29  
% 6.36/2.29  
% 6.36/2.29  %Background operators:
% 6.36/2.29  
% 6.36/2.29  
% 6.36/2.29  %Foreground operators:
% 6.36/2.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.36/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.36/2.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.36/2.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.36/2.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.36/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.36/2.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.36/2.29  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.36/2.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.36/2.29  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.36/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.36/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.36/2.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.36/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.36/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.36/2.29  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.36/2.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.36/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.36/2.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.36/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.36/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.36/2.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.36/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.36/2.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.36/2.29  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.36/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.36/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.36/2.29  
% 6.55/2.32  tff(f_208, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 6.55/2.32  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.55/2.32  tff(f_142, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.55/2.32  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.55/2.32  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.55/2.32  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.55/2.32  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.55/2.32  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.55/2.32  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.55/2.32  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.55/2.32  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.55/2.32  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.55/2.32  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.55/2.32  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.55/2.32  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.55/2.32  tff(f_140, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.55/2.32  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 6.55/2.32  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_338, plain, (![A_84, B_85, D_86]: (r2_relset_1(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.55/2.32  tff(c_349, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_338])).
% 6.55/2.32  tff(c_52, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.55/2.32  tff(c_12, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.55/2.32  tff(c_81, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 6.55/2.32  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.32  tff(c_82, plain, (![A_1]: (v1_relat_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 6.55/2.32  tff(c_112, plain, (![A_58]: (k1_relat_1(A_58)!=k1_xboole_0 | k1_xboole_0=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.32  tff(c_115, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))!=k1_xboole_0 | k6_partfun1(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_112])).
% 6.55/2.32  tff(c_117, plain, (![A_1]: (k1_xboole_0!=A_1 | k6_partfun1(A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_115])).
% 6.55/2.32  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_153, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_117, c_62])).
% 6.55/2.32  tff(c_272, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_153])).
% 6.55/2.32  tff(c_78, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_76, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_210, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.55/2.32  tff(c_223, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_210])).
% 6.55/2.32  tff(c_280, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.55/2.32  tff(c_292, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_280])).
% 6.55/2.32  tff(c_365, plain, (![B_90, A_91]: (k2_relat_1(B_90)=A_91 | ~v2_funct_2(B_90, A_91) | ~v5_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.32  tff(c_374, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_292, c_365])).
% 6.55/2.32  tff(c_386, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_374])).
% 6.55/2.32  tff(c_390, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_386])).
% 6.55/2.32  tff(c_74, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_593, plain, (![C_114, B_115, A_116]: (v2_funct_2(C_114, B_115) | ~v3_funct_2(C_114, A_116, B_115) | ~v1_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_605, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_593])).
% 6.55/2.32  tff(c_614, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_605])).
% 6.55/2.32  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_614])).
% 6.55/2.32  tff(c_617, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_386])).
% 6.55/2.32  tff(c_734, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.55/2.32  tff(c_746, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_734])).
% 6.55/2.32  tff(c_754, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_617, c_746])).
% 6.55/2.32  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.55/2.32  tff(c_348, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_338])).
% 6.55/2.32  tff(c_755, plain, (![C_132, A_133, B_134]: (v2_funct_1(C_132) | ~v3_funct_2(C_132, A_133, B_134) | ~v1_funct_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_767, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_755])).
% 6.55/2.32  tff(c_775, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_767])).
% 6.55/2.32  tff(c_1058, plain, (![C_171, D_173, B_174, E_170, A_169, F_172]: (k1_partfun1(A_169, B_174, C_171, D_173, E_170, F_172)=k5_relat_1(E_170, F_172) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_171, D_173))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_174))) | ~v1_funct_1(E_170))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.55/2.32  tff(c_1064, plain, (![A_169, B_174, E_170]: (k1_partfun1(A_169, B_174, '#skF_1', '#skF_1', E_170, '#skF_3')=k5_relat_1(E_170, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_169, B_174))) | ~v1_funct_1(E_170))), inference(resolution, [status(thm)], [c_64, c_1058])).
% 6.55/2.32  tff(c_1082, plain, (![A_177, B_178, E_179]: (k1_partfun1(A_177, B_178, '#skF_1', '#skF_1', E_179, '#skF_3')=k5_relat_1(E_179, '#skF_3') | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_1(E_179))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1064])).
% 6.55/2.32  tff(c_1094, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1082])).
% 6.55/2.32  tff(c_1102, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1094])).
% 6.55/2.32  tff(c_851, plain, (![D_143, C_144, A_145, B_146]: (D_143=C_144 | ~r2_relset_1(A_145, B_146, C_144, D_143) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.55/2.32  tff(c_865, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_851])).
% 6.55/2.32  tff(c_888, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_865])).
% 6.55/2.32  tff(c_889, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_888])).
% 6.55/2.32  tff(c_1109, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_889])).
% 6.55/2.32  tff(c_1123, plain, (![E_185, A_182, C_184, F_183, D_180, B_181]: (m1_subset_1(k1_partfun1(A_182, B_181, C_184, D_180, E_185, F_183), k1_zfmisc_1(k2_zfmisc_1(A_182, D_180))) | ~m1_subset_1(F_183, k1_zfmisc_1(k2_zfmisc_1(C_184, D_180))) | ~v1_funct_1(F_183) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))) | ~v1_funct_1(E_185))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.55/2.32  tff(c_1163, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1102, c_1123])).
% 6.55/2.32  tff(c_1181, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_64, c_1163])).
% 6.55/2.32  tff(c_1183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1109, c_1181])).
% 6.55/2.32  tff(c_1184, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_888])).
% 6.55/2.32  tff(c_2079, plain, (![C_240, D_241, B_242, A_243]: (k2_funct_1(C_240)=D_241 | k1_xboole_0=B_242 | k1_xboole_0=A_243 | ~v2_funct_1(C_240) | ~r2_relset_1(A_243, A_243, k1_partfun1(A_243, B_242, B_242, A_243, C_240, D_241), k6_partfun1(A_243)) | k2_relset_1(A_243, B_242, C_240)!=B_242 | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(B_242, A_243))) | ~v1_funct_2(D_241, B_242, A_243) | ~v1_funct_1(D_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))) | ~v1_funct_2(C_240, A_243, B_242) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.55/2.32  tff(c_2094, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1184, c_2079])).
% 6.55/2.32  tff(c_2111, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_64, c_754, c_348, c_775, c_2094])).
% 6.55/2.32  tff(c_2112, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_272, c_2111])).
% 6.55/2.32  tff(c_1193, plain, (![A_186, B_187]: (k2_funct_2(A_186, B_187)=k2_funct_1(B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_187, A_186, A_186) | ~v1_funct_2(B_187, A_186, A_186) | ~v1_funct_1(B_187))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.55/2.32  tff(c_1205, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_1193])).
% 6.55/2.32  tff(c_1213, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1205])).
% 6.55/2.32  tff(c_60, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_1218, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_60])).
% 6.55/2.32  tff(c_2115, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2112, c_1218])).
% 6.55/2.32  tff(c_2119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_349, c_2115])).
% 6.55/2.32  tff(c_2121, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_153])).
% 6.55/2.32  tff(c_222, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_210])).
% 6.55/2.32  tff(c_4, plain, (![A_2]: (k2_relat_1(A_2)!=k1_xboole_0 | k1_xboole_0=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.32  tff(c_238, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_222, c_4])).
% 6.55/2.32  tff(c_257, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_238])).
% 6.55/2.32  tff(c_2123, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_257])).
% 6.55/2.32  tff(c_2141, plain, (![C_245, B_246, A_247]: (v5_relat_1(C_245, B_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.55/2.32  tff(c_2152, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_2141])).
% 6.55/2.32  tff(c_2233, plain, (![B_258, A_259]: (k2_relat_1(B_258)=A_259 | ~v2_funct_2(B_258, A_259) | ~v5_relat_1(B_258, A_259) | ~v1_relat_1(B_258))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.32  tff(c_2245, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2152, c_2233])).
% 6.55/2.32  tff(c_2258, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2245])).
% 6.55/2.32  tff(c_2259, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2123, c_2258])).
% 6.55/2.32  tff(c_66, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.55/2.32  tff(c_2473, plain, (![C_279, B_280, A_281]: (v2_funct_2(C_279, B_280) | ~v3_funct_2(C_279, A_281, B_280) | ~v1_funct_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_2482, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2473])).
% 6.55/2.32  tff(c_2491, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2482])).
% 6.55/2.32  tff(c_2493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2259, c_2491])).
% 6.55/2.32  tff(c_2494, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_238])).
% 6.55/2.32  tff(c_120, plain, (![A_60]: (k1_xboole_0!=A_60 | k6_partfun1(A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_115])).
% 6.55/2.32  tff(c_132, plain, (![A_60]: (k1_relat_1(k1_xboole_0)=A_60 | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_120, c_81])).
% 6.55/2.32  tff(c_2554, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2494, c_132])).
% 6.55/2.32  tff(c_6, plain, (![A_2]: (k1_relat_1(A_2)!=k1_xboole_0 | k1_xboole_0=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.55/2.32  tff(c_239, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_222, c_6])).
% 6.55/2.32  tff(c_256, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_239])).
% 6.55/2.32  tff(c_2496, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_256])).
% 6.55/2.32  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2554, c_2496])).
% 6.55/2.32  tff(c_2558, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_239])).
% 6.55/2.32  tff(c_2601, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_153])).
% 6.55/2.32  tff(c_2602, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2601])).
% 6.55/2.32  tff(c_14, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.55/2.32  tff(c_80, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14])).
% 6.55/2.32  tff(c_135, plain, (![A_60]: (k2_relat_1(k1_xboole_0)=A_60 | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_120, c_80])).
% 6.55/2.32  tff(c_2579, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_135])).
% 6.55/2.32  tff(c_2640, plain, (![C_298, B_299, A_300]: (v5_relat_1(C_298, B_299) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_300, B_299))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.55/2.32  tff(c_2651, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_2640])).
% 6.55/2.32  tff(c_2743, plain, (![B_310, A_311]: (k2_relat_1(B_310)=A_311 | ~v2_funct_2(B_310, A_311) | ~v5_relat_1(B_310, A_311) | ~v1_relat_1(B_310))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.32  tff(c_2755, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2651, c_2743])).
% 6.55/2.32  tff(c_2767, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_2579, c_2755])).
% 6.55/2.32  tff(c_2768, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2602, c_2767])).
% 6.55/2.32  tff(c_2932, plain, (![C_328, B_329, A_330]: (v2_funct_2(C_328, B_329) | ~v3_funct_2(C_328, A_330, B_329) | ~v1_funct_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_2941, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2932])).
% 6.55/2.32  tff(c_2952, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2941])).
% 6.55/2.32  tff(c_2954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2768, c_2952])).
% 6.55/2.32  tff(c_2956, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2601])).
% 6.55/2.32  tff(c_2961, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_2558])).
% 6.55/2.32  tff(c_126, plain, (![A_60]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))) | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_120, c_46])).
% 6.55/2.32  tff(c_3478, plain, (![A_60]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))) | A_60!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2961, c_2961, c_126])).
% 6.55/2.32  tff(c_3535, plain, (![A_387, B_388, D_389]: (r2_relset_1(A_387, B_388, D_389, D_389) | ~m1_subset_1(D_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.55/2.32  tff(c_3549, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3478, c_3535])).
% 6.55/2.32  tff(c_2968, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_70])).
% 6.55/2.32  tff(c_254, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_223, c_4])).
% 6.55/2.32  tff(c_2981, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2961, c_2961, c_254])).
% 6.55/2.32  tff(c_2982, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2981])).
% 6.55/2.32  tff(c_2983, plain, (![C_331, B_332, A_333]: (v5_relat_1(C_331, B_332) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.55/2.32  tff(c_2991, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_2983])).
% 6.55/2.32  tff(c_3077, plain, (![B_343, A_344]: (k2_relat_1(B_343)=A_344 | ~v2_funct_2(B_343, A_344) | ~v5_relat_1(B_343, A_344) | ~v1_relat_1(B_343))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.32  tff(c_3086, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2991, c_3077])).
% 6.55/2.32  tff(c_3095, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_3086])).
% 6.55/2.32  tff(c_3096, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2982, c_3095])).
% 6.55/2.32  tff(c_3305, plain, (![C_366, B_367, A_368]: (v2_funct_2(C_366, B_367) | ~v3_funct_2(C_366, A_368, B_367) | ~v1_funct_1(C_366) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_368, B_367))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_3314, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_3305])).
% 6.55/2.32  tff(c_3322, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_3314])).
% 6.55/2.32  tff(c_3324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3096, c_3322])).
% 6.55/2.32  tff(c_3325, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2981])).
% 6.55/2.32  tff(c_3326, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2981])).
% 6.55/2.32  tff(c_3342, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_3326])).
% 6.55/2.32  tff(c_2962, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_222])).
% 6.55/2.32  tff(c_3611, plain, (![C_400, A_401, B_402]: (v2_funct_1(C_400) | ~v3_funct_2(C_400, A_401, B_402) | ~v1_funct_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.55/2.32  tff(c_3614, plain, (![A_60]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_60, A_60) | ~v1_funct_1('#skF_1') | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_3611])).
% 6.55/2.32  tff(c_3620, plain, (![A_60]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_60, A_60) | A_60!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3614])).
% 6.55/2.32  tff(c_3623, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3620])).
% 6.55/2.32  tff(c_2967, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_66])).
% 6.55/2.32  tff(c_3625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3623, c_2967])).
% 6.55/2.32  tff(c_3626, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_3620])).
% 6.55/2.32  tff(c_2559, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_239])).
% 6.55/2.32  tff(c_2574, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2559])).
% 6.55/2.32  tff(c_2960, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_2956, c_2574])).
% 6.55/2.32  tff(c_2567, plain, (![A_1]: (A_1!='#skF_3' | k6_partfun1(A_1)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_117])).
% 6.55/2.32  tff(c_3362, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_2956, c_2567])).
% 6.55/2.32  tff(c_16, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.55/2.32  tff(c_4603, plain, (![A_535, B_536]: (k2_funct_1(A_535)=B_536 | k6_partfun1(k2_relat_1(A_535))!=k5_relat_1(B_536, A_535) | k2_relat_1(B_536)!=k1_relat_1(A_535) | ~v2_funct_1(A_535) | ~v1_funct_1(B_536) | ~v1_relat_1(B_536) | ~v1_funct_1(A_535) | ~v1_relat_1(A_535))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 6.55/2.32  tff(c_4608, plain, (![B_536]: (k2_funct_1('#skF_1')=B_536 | k5_relat_1(B_536, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_536)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_536) | ~v1_relat_1(B_536) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3342, c_4603])).
% 6.55/2.32  tff(c_4615, plain, (![B_537]: (k2_funct_1('#skF_1')=B_537 | k5_relat_1(B_537, '#skF_1')!='#skF_1' | k2_relat_1(B_537)!='#skF_1' | ~v1_funct_1(B_537) | ~v1_relat_1(B_537))), inference(demodulation, [status(thm), theory('equality')], [c_2962, c_2968, c_3626, c_2960, c_3362, c_4608])).
% 6.55/2.32  tff(c_4618, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k2_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2962, c_4615])).
% 6.55/2.32  tff(c_4624, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3342, c_4618])).
% 6.55/2.32  tff(c_4627, plain, (k5_relat_1('#skF_1', '#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4624])).
% 6.55/2.32  tff(c_4702, plain, (![B_563, F_561, E_559, A_558, D_562, C_560]: (k1_partfun1(A_558, B_563, C_560, D_562, E_559, F_561)=k5_relat_1(E_559, F_561) | ~m1_subset_1(F_561, k1_zfmisc_1(k2_zfmisc_1(C_560, D_562))) | ~v1_funct_1(F_561) | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(A_558, B_563))) | ~v1_funct_1(E_559))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.55/2.32  tff(c_4704, plain, (![A_558, B_563, A_60, E_559]: (k1_partfun1(A_558, B_563, A_60, A_60, E_559, '#skF_1')=k5_relat_1(E_559, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(A_558, B_563))) | ~v1_funct_1(E_559) | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_4702])).
% 6.55/2.32  tff(c_4733, plain, (![A_572, B_573, A_574, E_575]: (k1_partfun1(A_572, B_573, A_574, A_574, E_575, '#skF_1')=k5_relat_1(E_575, '#skF_1') | ~m1_subset_1(E_575, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))) | ~v1_funct_1(E_575) | A_574!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_4704])).
% 6.55/2.32  tff(c_4735, plain, (![A_60, A_574]: (k1_partfun1(A_60, A_60, A_574, A_574, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1') | A_574!='#skF_1' | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_4733])).
% 6.55/2.32  tff(c_4743, plain, (![A_576, A_577]: (k1_partfun1(A_576, A_576, A_577, A_577, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | A_577!='#skF_1' | A_576!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_4735])).
% 6.55/2.32  tff(c_3361, plain, (![A_1]: (A_1!='#skF_1' | k6_partfun1(A_1)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_2956, c_2567])).
% 6.55/2.32  tff(c_3799, plain, (![F_442, C_441, D_443, B_444, E_440, A_439]: (k1_partfun1(A_439, B_444, C_441, D_443, E_440, F_442)=k5_relat_1(E_440, F_442) | ~m1_subset_1(F_442, k1_zfmisc_1(k2_zfmisc_1(C_441, D_443))) | ~v1_funct_1(F_442) | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(A_439, B_444))) | ~v1_funct_1(E_440))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.55/2.32  tff(c_3801, plain, (![A_439, B_444, A_60, E_440]: (k1_partfun1(A_439, B_444, A_60, A_60, E_440, '#skF_1')=k5_relat_1(E_440, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_440, k1_zfmisc_1(k2_zfmisc_1(A_439, B_444))) | ~v1_funct_1(E_440) | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_3799])).
% 6.55/2.32  tff(c_3830, plain, (![A_453, B_454, A_455, E_456]: (k1_partfun1(A_453, B_454, A_455, A_455, E_456, '#skF_1')=k5_relat_1(E_456, '#skF_1') | ~m1_subset_1(E_456, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | ~v1_funct_1(E_456) | A_455!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3801])).
% 6.55/2.32  tff(c_3950, plain, (![A_473, A_474]: (k1_partfun1(A_473, A_473, A_474, A_474, k6_partfun1(A_473), '#skF_1')=k5_relat_1(k6_partfun1(A_473), '#skF_1') | ~v1_funct_1(k6_partfun1(A_473)) | A_474!='#skF_1')), inference(resolution, [status(thm)], [c_46, c_3830])).
% 6.55/2.32  tff(c_3952, plain, (![A_1, A_474]: (k1_partfun1(A_1, A_1, A_474, A_474, k6_partfun1(A_1), '#skF_1')=k5_relat_1(k6_partfun1(A_1), '#skF_1') | ~v1_funct_1('#skF_1') | A_474!='#skF_1' | A_1!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3361, c_3950])).
% 6.55/2.32  tff(c_3956, plain, (![A_475, A_476]: (k1_partfun1(A_475, A_475, A_476, A_476, k6_partfun1(A_475), '#skF_1')=k5_relat_1(k6_partfun1(A_475), '#skF_1') | A_476!='#skF_1' | A_475!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3952])).
% 6.55/2.32  tff(c_40, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.55/2.32  tff(c_3970, plain, (![A_475, A_476]: (m1_subset_1(k5_relat_1(k6_partfun1(A_475), '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(A_475, A_476))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_476, A_476))) | ~v1_funct_1('#skF_1') | ~m1_subset_1(k6_partfun1(A_475), k1_zfmisc_1(k2_zfmisc_1(A_475, A_475))) | ~v1_funct_1(k6_partfun1(A_475)) | A_476!='#skF_1' | A_475!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3956, c_40])).
% 6.55/2.32  tff(c_4172, plain, (![A_494, A_495]: (m1_subset_1(k5_relat_1(k6_partfun1(A_494), '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(A_494, A_495))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_495, A_495))) | ~v1_funct_1(k6_partfun1(A_494)) | A_495!='#skF_1' | A_494!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2968, c_3970])).
% 6.55/2.32  tff(c_4177, plain, (![A_496, A_497]: (m1_subset_1(k5_relat_1(k6_partfun1(A_496), '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(A_496, A_497))) | ~v1_funct_1(k6_partfun1(A_496)) | A_496!='#skF_1' | A_497!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_4172])).
% 6.55/2.32  tff(c_4514, plain, (![A_529, A_530]: (m1_subset_1(k5_relat_1('#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(A_529, A_530))) | ~v1_funct_1(k6_partfun1(A_529)) | A_529!='#skF_1' | A_530!='#skF_1' | A_529!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3361, c_4177])).
% 6.55/2.32  tff(c_3832, plain, (![A_60, A_455]: (k1_partfun1(A_60, A_60, A_455, A_455, '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1') | A_455!='#skF_1' | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_3830])).
% 6.55/2.32  tff(c_3839, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3832])).
% 6.55/2.32  tff(c_3479, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2961, c_2961, c_126])).
% 6.55/2.32  tff(c_2963, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_62])).
% 6.55/2.32  tff(c_3534, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_3325, c_2963])).
% 6.55/2.32  tff(c_3650, plain, (![D_408, C_409, A_410, B_411]: (D_408=C_409 | ~r2_relset_1(A_410, B_411, C_409, D_408) | ~m1_subset_1(D_408, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.55/2.32  tff(c_3660, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_3534, c_3650])).
% 6.55/2.32  tff(c_3675, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3479, c_3660])).
% 6.55/2.32  tff(c_3676, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3675])).
% 6.55/2.32  tff(c_3840, plain, (~m1_subset_1(k5_relat_1('#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3839, c_3676])).
% 6.55/2.32  tff(c_4521, plain, (~v1_funct_1(k6_partfun1('#skF_1'))), inference(resolution, [status(thm)], [c_4514, c_3840])).
% 6.55/2.32  tff(c_4565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2968, c_3362, c_4521])).
% 6.55/2.32  tff(c_4566, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_3675])).
% 6.55/2.32  tff(c_4752, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4743, c_4566])).
% 6.55/2.32  tff(c_4763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4627, c_4752])).
% 6.55/2.32  tff(c_4764, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_4624])).
% 6.55/2.32  tff(c_2966, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_68])).
% 6.55/2.32  tff(c_4575, plain, (![A_531, B_532]: (k2_funct_2(A_531, B_532)=k2_funct_1(B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(k2_zfmisc_1(A_531, A_531))) | ~v3_funct_2(B_532, A_531, A_531) | ~v1_funct_2(B_532, A_531, A_531) | ~v1_funct_1(B_532))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.55/2.32  tff(c_4578, plain, (![A_60]: (k2_funct_2(A_60, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_60, A_60) | ~v1_funct_2('#skF_1', A_60, A_60) | ~v1_funct_1('#skF_1') | A_60!='#skF_1')), inference(resolution, [status(thm)], [c_3478, c_4575])).
% 6.55/2.32  tff(c_4587, plain, (![A_533]: (k2_funct_2(A_533, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_533, A_533) | ~v1_funct_2('#skF_1', A_533, A_533) | A_533!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_4578])).
% 6.55/2.32  tff(c_4590, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2967, c_4587])).
% 6.55/2.32  tff(c_4593, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2966, c_4590])).
% 6.55/2.32  tff(c_2964, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_60])).
% 6.55/2.32  tff(c_3444, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3325, c_2964])).
% 6.55/2.32  tff(c_4594, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4593, c_3444])).
% 6.55/2.32  tff(c_4776, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4764, c_4594])).
% 6.55/2.32  tff(c_4781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3549, c_4776])).
% 6.55/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.55/2.32  
% 6.55/2.32  Inference rules
% 6.55/2.32  ----------------------
% 6.55/2.32  #Ref     : 12
% 6.55/2.32  #Sup     : 948
% 6.55/2.32  #Fact    : 0
% 6.55/2.32  #Define  : 0
% 6.55/2.32  #Split   : 42
% 6.55/2.32  #Chain   : 0
% 6.55/2.32  #Close   : 0
% 6.55/2.32  
% 6.55/2.32  Ordering : KBO
% 6.55/2.32  
% 6.55/2.32  Simplification rules
% 6.55/2.32  ----------------------
% 6.55/2.32  #Subsume      : 342
% 6.55/2.32  #Demod        : 932
% 6.55/2.32  #Tautology    : 331
% 6.55/2.32  #SimpNegUnit  : 96
% 6.55/2.32  #BackRed      : 102
% 6.55/2.32  
% 6.55/2.32  #Partial instantiations: 0
% 6.55/2.32  #Strategies tried      : 1
% 6.55/2.32  
% 6.55/2.32  Timing (in seconds)
% 6.55/2.32  ----------------------
% 6.55/2.32  Preprocessing        : 0.38
% 6.55/2.32  Parsing              : 0.20
% 6.55/2.32  CNF conversion       : 0.03
% 6.55/2.32  Main loop            : 1.10
% 6.55/2.32  Inferencing          : 0.37
% 6.55/2.32  Reduction            : 0.40
% 6.55/2.32  Demodulation         : 0.27
% 6.55/2.32  BG Simplification    : 0.04
% 6.55/2.32  Subsumption          : 0.19
% 6.55/2.32  Abstraction          : 0.05
% 6.55/2.32  MUC search           : 0.00
% 6.55/2.33  Cooper               : 0.00
% 6.55/2.33  Total                : 1.55
% 6.55/2.33  Index Insertion      : 0.00
% 6.55/2.33  Index Deletion       : 0.00
% 6.55/2.33  Index Matching       : 0.00
% 6.55/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
