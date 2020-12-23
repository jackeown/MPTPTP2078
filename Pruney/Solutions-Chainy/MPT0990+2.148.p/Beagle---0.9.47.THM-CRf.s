%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:18 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 794 expanded)
%              Number of leaves         :   41 ( 298 expanded)
%              Depth                    :   18
%              Number of atoms          :  328 (3286 expanded)
%              Number of equality atoms :  116 (1175 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_215,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_172,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_112,axiom,(
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

tff(f_130,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_160,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_189,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_114,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_120,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_114])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_195,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_206,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_195])).

tff(c_266,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_272,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_266])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_206,c_272])).

tff(c_281,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_280])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_164,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_164])).

tff(c_176,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_170])).

tff(c_62,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_32,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_632,plain,(
    ! [A_137,B_138] :
      ( k2_funct_1(A_137) = B_138
      | k6_partfun1(k2_relat_1(A_137)) != k5_relat_1(B_138,A_137)
      | k2_relat_1(B_138) != k1_relat_1(A_137)
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_638,plain,(
    ! [B_138] :
      ( k2_funct_1('#skF_3') = B_138
      | k5_relat_1(B_138,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_138) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_632])).

tff(c_645,plain,(
    ! [B_139] :
      ( k2_funct_1('#skF_3') = B_139
      | k5_relat_1(B_139,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_139) != '#skF_1'
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_88,c_72,c_281,c_638])).

tff(c_648,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_645])).

tff(c_663,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_648])).

tff(c_664,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_663])).

tff(c_671,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_42,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_89,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_42])).

tff(c_134,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_relset_1(A_61,B_62,D_63,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_141,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_89,c_134])).

tff(c_177,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_164])).

tff(c_473,plain,(
    ! [F_120,E_122,B_119,D_121,A_118,C_123] :
      ( k1_partfun1(A_118,B_119,C_123,D_121,E_122,F_120) = k5_relat_1(E_122,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_123,D_121)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_479,plain,(
    ! [A_118,B_119,E_122] :
      ( k1_partfun1(A_118,B_119,'#skF_2','#skF_1',E_122,'#skF_4') = k5_relat_1(E_122,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(E_122) ) ),
    inference(resolution,[status(thm)],[c_78,c_473])).

tff(c_515,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_479])).

tff(c_521,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_515])).

tff(c_528,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_521])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_356,plain,(
    ! [D_96,C_97,A_98,B_99] :
      ( D_96 = C_97
      | ~ r2_relset_1(A_98,B_99,C_97,D_96)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_364,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_356])).

tff(c_379,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_364])).

tff(c_380,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_533,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_380])).

tff(c_539,plain,(
    ! [A_134,F_135,C_136,E_133,B_132,D_131] :
      ( m1_subset_1(k1_partfun1(A_134,B_132,C_136,D_131,E_133,F_135),k1_zfmisc_1(k2_zfmisc_1(A_134,D_131)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_131)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_587,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_539])).

tff(c_612,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_587])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_612])).

tff(c_623,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_983,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_relset_1(A_170,B_171,C_172) = B_171
      | ~ r2_relset_1(B_171,B_171,k1_partfun1(B_171,A_170,A_170,B_171,D_173,C_172),k6_partfun1(B_171))
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(B_171,A_170)))
      | ~ v1_funct_2(D_173,B_171,A_170)
      | ~ v1_funct_1(D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_172,A_170,B_171)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_989,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_983])).

tff(c_993,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_141,c_177,c_989])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_993])).

tff(c_996,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_207,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_195])).

tff(c_275,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_266])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_207,c_275])).

tff(c_285,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_284])).

tff(c_997,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_90,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_partfun1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_1001,plain,(
    ! [B_16] :
      ( k2_funct_1('#skF_4') = B_16
      | k5_relat_1(B_16,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_16) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_90])).

tff(c_1005,plain,(
    ! [B_16] :
      ( k2_funct_1('#skF_4') = B_16
      | k5_relat_1(B_16,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_16) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_285,c_1001])).

tff(c_1013,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_1074,plain,(
    ! [F_192,A_190,B_191,C_195,D_193,E_194] :
      ( k1_partfun1(A_190,B_191,C_195,D_193,E_194,F_192) = k5_relat_1(E_194,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_195,D_193)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1080,plain,(
    ! [A_190,B_191,E_194] :
      ( k1_partfun1(A_190,B_191,'#skF_2','#skF_1',E_194,'#skF_4') = k5_relat_1(E_194,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(E_194) ) ),
    inference(resolution,[status(thm)],[c_78,c_1074])).

tff(c_1434,plain,(
    ! [A_210,B_211,E_212] :
      ( k1_partfun1(A_210,B_211,'#skF_2','#skF_1',E_212,'#skF_4') = k5_relat_1(E_212,'#skF_4')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(E_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1080])).

tff(c_1452,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1434])).

tff(c_1469,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_623,c_1452])).

tff(c_20,plain,(
    ! [A_9,B_11] :
      ( v2_funct_1(A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(k5_relat_1(B_11,A_9))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1476,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_20])).

tff(c_1483,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_129,c_88,c_93,c_176,c_285,c_1476])).

tff(c_1485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_1483])).

tff(c_1487,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_1488,plain,(
    ! [B_213] :
      ( k2_funct_1('#skF_4') = B_213
      | k5_relat_1(B_213,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_213) != '#skF_2'
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213) ) ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_1494,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_1488])).

tff(c_1509,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_176,c_1494])).

tff(c_1513,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_1588,plain,(
    ! [C_238,B_234,F_235,A_233,E_237,D_236] :
      ( k1_partfun1(A_233,B_234,C_238,D_236,E_237,F_235) = k5_relat_1(E_237,F_235)
      | ~ m1_subset_1(F_235,k1_zfmisc_1(k2_zfmisc_1(C_238,D_236)))
      | ~ v1_funct_1(F_235)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1594,plain,(
    ! [A_233,B_234,E_237] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_78,c_1588])).

tff(c_1884,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_2','#skF_1',E_255,'#skF_4') = k5_relat_1(E_255,'#skF_4')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1594])).

tff(c_1899,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1884])).

tff(c_1913,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_623,c_1899])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1513,c_1913])).

tff(c_1916,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_30,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_relat_1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_91,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k2_funct_1(A_13)) = k6_partfun1(k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30])).

tff(c_1922,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1916,c_91])).

tff(c_1944,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_1487,c_285,c_1922])).

tff(c_1946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.79  
% 4.55/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.79  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.79  
% 4.55/1.79  %Foreground sorts:
% 4.55/1.79  
% 4.55/1.79  
% 4.55/1.79  %Background operators:
% 4.55/1.79  
% 4.55/1.79  
% 4.55/1.79  %Foreground operators:
% 4.55/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.55/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.55/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.55/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.55/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.55/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.55/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.79  
% 4.71/1.81  tff(f_215, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.71/1.81  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.71/1.81  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.71/1.81  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.71/1.81  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.71/1.81  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.71/1.81  tff(f_172, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.71/1.81  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.71/1.81  tff(f_130, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.72/1.81  tff(f_128, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.72/1.81  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.72/1.81  tff(f_160, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.72/1.81  tff(f_189, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.72/1.81  tff(f_46, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.72/1.81  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.72/1.81  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.72/1.81  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.72/1.81  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_114, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.81  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_114])).
% 4.72/1.81  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 4.72/1.81  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_114])).
% 4.72/1.81  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 4.72/1.81  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_195, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.72/1.81  tff(c_206, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_195])).
% 4.72/1.81  tff(c_266, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.72/1.81  tff(c_272, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_84, c_266])).
% 4.72/1.81  tff(c_280, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_206, c_272])).
% 4.72/1.81  tff(c_281, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_280])).
% 4.72/1.81  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.81  tff(c_164, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.72/1.81  tff(c_170, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_164])).
% 4.72/1.81  tff(c_176, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_170])).
% 4.72/1.81  tff(c_62, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.72/1.81  tff(c_32, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.72/1.81  tff(c_632, plain, (![A_137, B_138]: (k2_funct_1(A_137)=B_138 | k6_partfun1(k2_relat_1(A_137))!=k5_relat_1(B_138, A_137) | k2_relat_1(B_138)!=k1_relat_1(A_137) | ~v2_funct_1(A_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 4.72/1.82  tff(c_638, plain, (![B_138]: (k2_funct_1('#skF_3')=B_138 | k5_relat_1(B_138, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_138)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_632])).
% 4.72/1.82  tff(c_645, plain, (![B_139]: (k2_funct_1('#skF_3')=B_139 | k5_relat_1(B_139, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_139)!='#skF_1' | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_88, c_72, c_281, c_638])).
% 4.72/1.82  tff(c_648, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_645])).
% 4.72/1.82  tff(c_663, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_648])).
% 4.72/1.82  tff(c_664, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_663])).
% 4.72/1.82  tff(c_671, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_664])).
% 4.72/1.82  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.82  tff(c_42, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.72/1.82  tff(c_89, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_42])).
% 4.72/1.82  tff(c_134, plain, (![A_61, B_62, D_63]: (r2_relset_1(A_61, B_62, D_63, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.72/1.82  tff(c_141, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_89, c_134])).
% 4.72/1.82  tff(c_177, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_164])).
% 4.72/1.82  tff(c_473, plain, (![F_120, E_122, B_119, D_121, A_118, C_123]: (k1_partfun1(A_118, B_119, C_123, D_121, E_122, F_120)=k5_relat_1(E_122, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_123, D_121))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.72/1.82  tff(c_479, plain, (![A_118, B_119, E_122]: (k1_partfun1(A_118, B_119, '#skF_2', '#skF_1', E_122, '#skF_4')=k5_relat_1(E_122, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(E_122))), inference(resolution, [status(thm)], [c_78, c_473])).
% 4.72/1.82  tff(c_515, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_479])).
% 4.72/1.82  tff(c_521, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_515])).
% 4.72/1.82  tff(c_528, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_521])).
% 4.72/1.82  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.82  tff(c_356, plain, (![D_96, C_97, A_98, B_99]: (D_96=C_97 | ~r2_relset_1(A_98, B_99, C_97, D_96) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.72/1.82  tff(c_364, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_356])).
% 4.72/1.82  tff(c_379, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_364])).
% 4.72/1.82  tff(c_380, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_379])).
% 4.72/1.82  tff(c_533, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_380])).
% 4.72/1.82  tff(c_539, plain, (![A_134, F_135, C_136, E_133, B_132, D_131]: (m1_subset_1(k1_partfun1(A_134, B_132, C_136, D_131, E_133, F_135), k1_zfmisc_1(k2_zfmisc_1(A_134, D_131))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_131))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.82  tff(c_587, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_528, c_539])).
% 4.72/1.82  tff(c_612, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_587])).
% 4.72/1.82  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_612])).
% 4.72/1.82  tff(c_623, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_379])).
% 4.72/1.82  tff(c_983, plain, (![A_170, B_171, C_172, D_173]: (k2_relset_1(A_170, B_171, C_172)=B_171 | ~r2_relset_1(B_171, B_171, k1_partfun1(B_171, A_170, A_170, B_171, D_173, C_172), k6_partfun1(B_171)) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(B_171, A_170))) | ~v1_funct_2(D_173, B_171, A_170) | ~v1_funct_1(D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_172, A_170, B_171) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.72/1.82  tff(c_989, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_623, c_983])).
% 4.72/1.82  tff(c_993, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_141, c_177, c_989])).
% 4.72/1.82  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_671, c_993])).
% 4.72/1.82  tff(c_996, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_664])).
% 4.72/1.82  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_215])).
% 4.72/1.82  tff(c_207, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_195])).
% 4.72/1.82  tff(c_275, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_266])).
% 4.72/1.82  tff(c_284, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_207, c_275])).
% 4.72/1.82  tff(c_285, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_70, c_284])).
% 4.72/1.82  tff(c_997, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_664])).
% 4.72/1.82  tff(c_90, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_partfun1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 4.72/1.82  tff(c_1001, plain, (![B_16]: (k2_funct_1('#skF_4')=B_16 | k5_relat_1(B_16, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_16)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_997, c_90])).
% 4.72/1.82  tff(c_1005, plain, (![B_16]: (k2_funct_1('#skF_4')=B_16 | k5_relat_1(B_16, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_16)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_285, c_1001])).
% 4.72/1.82  tff(c_1013, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1005])).
% 4.72/1.82  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/1.82  tff(c_93, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 4.72/1.82  tff(c_1074, plain, (![F_192, A_190, B_191, C_195, D_193, E_194]: (k1_partfun1(A_190, B_191, C_195, D_193, E_194, F_192)=k5_relat_1(E_194, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_195, D_193))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.72/1.82  tff(c_1080, plain, (![A_190, B_191, E_194]: (k1_partfun1(A_190, B_191, '#skF_2', '#skF_1', E_194, '#skF_4')=k5_relat_1(E_194, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(E_194))), inference(resolution, [status(thm)], [c_78, c_1074])).
% 4.72/1.82  tff(c_1434, plain, (![A_210, B_211, E_212]: (k1_partfun1(A_210, B_211, '#skF_2', '#skF_1', E_212, '#skF_4')=k5_relat_1(E_212, '#skF_4') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(E_212))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1080])).
% 4.72/1.82  tff(c_1452, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1434])).
% 4.72/1.82  tff(c_1469, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_623, c_1452])).
% 4.72/1.82  tff(c_20, plain, (![A_9, B_11]: (v2_funct_1(A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(k5_relat_1(B_11, A_9)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.72/1.82  tff(c_1476, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1469, c_20])).
% 4.72/1.82  tff(c_1483, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_129, c_88, c_93, c_176, c_285, c_1476])).
% 4.72/1.82  tff(c_1485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1013, c_1483])).
% 4.72/1.82  tff(c_1487, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1005])).
% 4.72/1.82  tff(c_1488, plain, (![B_213]: (k2_funct_1('#skF_4')=B_213 | k5_relat_1(B_213, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_213)!='#skF_2' | ~v1_funct_1(B_213) | ~v1_relat_1(B_213))), inference(splitRight, [status(thm)], [c_1005])).
% 4.72/1.82  tff(c_1494, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_1488])).
% 4.72/1.82  tff(c_1509, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_176, c_1494])).
% 4.72/1.82  tff(c_1513, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1509])).
% 4.72/1.82  tff(c_1588, plain, (![C_238, B_234, F_235, A_233, E_237, D_236]: (k1_partfun1(A_233, B_234, C_238, D_236, E_237, F_235)=k5_relat_1(E_237, F_235) | ~m1_subset_1(F_235, k1_zfmisc_1(k2_zfmisc_1(C_238, D_236))) | ~v1_funct_1(F_235) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.72/1.82  tff(c_1594, plain, (![A_233, B_234, E_237]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_78, c_1588])).
% 4.72/1.82  tff(c_1884, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_2', '#skF_1', E_255, '#skF_4')=k5_relat_1(E_255, '#skF_4') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1594])).
% 4.72/1.82  tff(c_1899, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1884])).
% 4.72/1.82  tff(c_1913, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_623, c_1899])).
% 4.72/1.82  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1513, c_1913])).
% 4.72/1.82  tff(c_1916, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1509])).
% 4.72/1.82  tff(c_30, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_relat_1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.72/1.82  tff(c_91, plain, (![A_13]: (k5_relat_1(A_13, k2_funct_1(A_13))=k6_partfun1(k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30])).
% 4.72/1.82  tff(c_1922, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1916, c_91])).
% 4.72/1.82  tff(c_1944, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_1487, c_285, c_1922])).
% 4.72/1.82  tff(c_1946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_1944])).
% 4.72/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.82  
% 4.72/1.82  Inference rules
% 4.72/1.82  ----------------------
% 4.72/1.82  #Ref     : 0
% 4.72/1.82  #Sup     : 393
% 4.72/1.82  #Fact    : 0
% 4.72/1.82  #Define  : 0
% 4.72/1.82  #Split   : 17
% 4.72/1.82  #Chain   : 0
% 4.72/1.82  #Close   : 0
% 4.72/1.82  
% 4.72/1.82  Ordering : KBO
% 4.72/1.82  
% 4.72/1.82  Simplification rules
% 4.72/1.82  ----------------------
% 4.72/1.82  #Subsume      : 7
% 4.72/1.82  #Demod        : 308
% 4.72/1.82  #Tautology    : 101
% 4.72/1.82  #SimpNegUnit  : 27
% 4.72/1.82  #BackRed      : 18
% 4.72/1.82  
% 4.72/1.82  #Partial instantiations: 0
% 4.72/1.82  #Strategies tried      : 1
% 4.72/1.82  
% 4.72/1.82  Timing (in seconds)
% 4.72/1.82  ----------------------
% 4.72/1.82  Preprocessing        : 0.37
% 4.72/1.82  Parsing              : 0.19
% 4.72/1.82  CNF conversion       : 0.03
% 4.72/1.82  Main loop            : 0.67
% 4.72/1.82  Inferencing          : 0.25
% 4.72/1.82  Reduction            : 0.22
% 4.72/1.82  Demodulation         : 0.16
% 4.72/1.82  BG Simplification    : 0.04
% 4.72/1.82  Subsumption          : 0.11
% 4.72/1.82  Abstraction          : 0.03
% 4.72/1.82  MUC search           : 0.00
% 4.72/1.82  Cooper               : 0.00
% 4.72/1.82  Total                : 1.09
% 4.72/1.82  Index Insertion      : 0.00
% 4.72/1.82  Index Deletion       : 0.00
% 4.72/1.82  Index Matching       : 0.00
% 4.72/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
