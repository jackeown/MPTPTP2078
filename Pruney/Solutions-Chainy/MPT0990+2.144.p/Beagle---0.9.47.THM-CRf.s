%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:17 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 704 expanded)
%              Number of leaves         :   44 ( 268 expanded)
%              Depth                    :   19
%              Number of atoms          :  319 (2895 expanded)
%              Number of equality atoms :  116 (1017 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_189,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_146,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_84,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_163,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_67,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_115,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_115])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_115])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_134,plain,(
    ! [A_58] :
      ( k4_relat_1(A_58) = k2_funct_1(A_58)
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_134])).

tff(c_146,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_140])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_206,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_212,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_206])).

tff(c_218,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_212])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_175,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_187,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_175])).

tff(c_261,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_261])).

tff(c_279,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_187,c_270])).

tff(c_280,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_279])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_186,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_175])).

tff(c_267,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_261])).

tff(c_275,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_186,c_267])).

tff(c_276,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_275])).

tff(c_50,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_568,plain,(
    ! [A_137,B_138] :
      ( k2_funct_1(A_137) = B_138
      | k6_partfun1(k2_relat_1(A_137)) != k5_relat_1(B_138,A_137)
      | k2_relat_1(B_138) != k1_relat_1(A_137)
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_570,plain,(
    ! [B_138] :
      ( k2_funct_1('#skF_3') = B_138
      | k5_relat_1(B_138,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_138) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_568])).

tff(c_573,plain,(
    ! [B_139] :
      ( k2_funct_1('#skF_3') = B_139
      | k5_relat_1(B_139,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_139) != '#skF_1'
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_60,c_276,c_570])).

tff(c_576,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_573])).

tff(c_588,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_576])).

tff(c_589,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_588])).

tff(c_595,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_46,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_164,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_171,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_219,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_206])).

tff(c_495,plain,(
    ! [E_132,A_133,F_131,D_136,C_134,B_135] :
      ( m1_subset_1(k1_partfun1(A_133,B_135,C_134,D_136,E_132,F_131),k1_zfmisc_1(k2_zfmisc_1(A_133,D_136)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_134,D_136)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_135)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_331,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_339,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_331])).

tff(c_354,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_339])).

tff(c_355,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_513,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_495,c_355])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_513])).

tff(c_559,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_936,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k2_relset_1(A_171,B_172,C_173) = B_172
      | ~ r2_relset_1(B_172,B_172,k1_partfun1(B_172,A_171,A_171,B_172,D_174,C_173),k6_partfun1(B_172))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_172,A_171)))
      | ~ v1_funct_2(D_174,B_172,A_171)
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_942,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_936])).

tff(c_946,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_171,c_219,c_942])).

tff(c_948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_946])).

tff(c_950,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_77,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_954,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_77])).

tff(c_958,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_280,c_954])).

tff(c_966,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_12,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_1042,plain,(
    ! [A_191,C_193,F_192,D_195,B_196,E_194] :
      ( k1_partfun1(A_191,B_196,C_193,D_195,E_194,F_192) = k5_relat_1(E_194,F_192)
      | ~ m1_subset_1(F_192,k1_zfmisc_1(k2_zfmisc_1(C_193,D_195)))
      | ~ v1_funct_1(F_192)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_191,B_196)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1048,plain,(
    ! [A_191,B_196,E_194] :
      ( k1_partfun1(A_191,B_196,'#skF_2','#skF_1',E_194,'#skF_4') = k5_relat_1(E_194,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_191,B_196)))
      | ~ v1_funct_1(E_194) ) ),
    inference(resolution,[status(thm)],[c_66,c_1042])).

tff(c_1331,plain,(
    ! [A_212,B_213,E_214] :
      ( k1_partfun1(A_212,B_213,'#skF_2','#skF_1',E_214,'#skF_4') = k5_relat_1(E_214,'#skF_4')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_1(E_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1048])).

tff(c_1346,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1331])).

tff(c_1360,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_559,c_1346])).

tff(c_14,plain,(
    ! [A_9,B_11] :
      ( v2_funct_1(A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(k5_relat_1(B_11,A_9))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1370,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_14])).

tff(c_1376,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_130,c_76,c_78,c_218,c_280,c_1370])).

tff(c_1378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_1376])).

tff(c_1396,plain,(
    ! [B_215] :
      ( k2_funct_1('#skF_4') = B_215
      | k5_relat_1(B_215,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_215) != '#skF_2'
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1402,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_1396])).

tff(c_1414,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_218,c_1402])).

tff(c_1425,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1414])).

tff(c_1506,plain,(
    ! [B_237,C_234,A_232,E_235,D_236,F_233] :
      ( k1_partfun1(A_232,B_237,C_234,D_236,E_235,F_233) = k5_relat_1(E_235,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_234,D_236)))
      | ~ v1_funct_1(F_233)
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_232,B_237)))
      | ~ v1_funct_1(E_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1512,plain,(
    ! [A_232,B_237,E_235] :
      ( k1_partfun1(A_232,B_237,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_232,B_237)))
      | ~ v1_funct_1(E_235) ) ),
    inference(resolution,[status(thm)],[c_66,c_1506])).

tff(c_1796,plain,(
    ! [A_252,B_253,E_254] :
      ( k1_partfun1(A_252,B_253,'#skF_2','#skF_1',E_254,'#skF_4') = k5_relat_1(E_254,'#skF_4')
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_1(E_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1512])).

tff(c_1811,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1796])).

tff(c_1825,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_559,c_1811])).

tff(c_1827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1425,c_1825])).

tff(c_1828,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_1380,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_8,plain,(
    ! [A_7] :
      ( k4_relat_1(A_7) = k2_funct_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1383,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1380,c_8])).

tff(c_1386,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_1383])).

tff(c_1832,plain,(
    k4_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_1386])).

tff(c_6,plain,(
    ! [A_6] :
      ( k4_relat_1(k4_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1840,plain,
    ( k4_relat_1('#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_6])).

tff(c_1844,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_146,c_1840])).

tff(c_1846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.80  
% 4.60/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.81  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.81  
% 4.60/1.81  %Foreground sorts:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Background operators:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Foreground operators:
% 4.60/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.60/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.60/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.60/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.60/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.60/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.60/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.81  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.60/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.81  
% 4.77/1.83  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.77/1.83  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.77/1.83  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.77/1.83  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.77/1.83  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.77/1.83  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.77/1.83  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.77/1.83  tff(f_146, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.77/1.83  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.77/1.83  tff(f_134, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.77/1.83  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.77/1.83  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.77/1.83  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.77/1.83  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.77/1.83  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.77/1.83  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.77/1.83  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.77/1.83  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.77/1.83  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_115, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.83  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_115])).
% 4.77/1.83  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 4.77/1.83  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_115])).
% 4.77/1.83  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 4.77/1.83  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_134, plain, (![A_58]: (k4_relat_1(A_58)=k2_funct_1(A_58) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.83  tff(c_140, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_134])).
% 4.77/1.83  tff(c_146, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_140])).
% 4.77/1.83  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_206, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.77/1.83  tff(c_212, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_206])).
% 4.77/1.83  tff(c_218, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_212])).
% 4.77/1.83  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_175, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.77/1.83  tff(c_187, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_175])).
% 4.77/1.83  tff(c_261, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.77/1.83  tff(c_270, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_261])).
% 4.77/1.83  tff(c_279, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_187, c_270])).
% 4.77/1.83  tff(c_280, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_279])).
% 4.77/1.83  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_186, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_175])).
% 4.77/1.83  tff(c_267, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_261])).
% 4.77/1.83  tff(c_275, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_186, c_267])).
% 4.77/1.83  tff(c_276, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_275])).
% 4.77/1.83  tff(c_50, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.77/1.83  tff(c_18, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.83  tff(c_568, plain, (![A_137, B_138]: (k2_funct_1(A_137)=B_138 | k6_partfun1(k2_relat_1(A_137))!=k5_relat_1(B_138, A_137) | k2_relat_1(B_138)!=k1_relat_1(A_137) | ~v2_funct_1(A_137) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 4.77/1.83  tff(c_570, plain, (![B_138]: (k2_funct_1('#skF_3')=B_138 | k5_relat_1(B_138, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_138)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_138) | ~v1_relat_1(B_138) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_568])).
% 4.77/1.83  tff(c_573, plain, (![B_139]: (k2_funct_1('#skF_3')=B_139 | k5_relat_1(B_139, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_139)!='#skF_1' | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_60, c_276, c_570])).
% 4.77/1.83  tff(c_576, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_573])).
% 4.77/1.83  tff(c_588, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_576])).
% 4.77/1.83  tff(c_589, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_588])).
% 4.77/1.83  tff(c_595, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_589])).
% 4.77/1.83  tff(c_46, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.77/1.83  tff(c_164, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.77/1.83  tff(c_171, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_46, c_164])).
% 4.77/1.83  tff(c_219, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_206])).
% 4.77/1.83  tff(c_495, plain, (![E_132, A_133, F_131, D_136, C_134, B_135]: (m1_subset_1(k1_partfun1(A_133, B_135, C_134, D_136, E_132, F_131), k1_zfmisc_1(k2_zfmisc_1(A_133, D_136))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_134, D_136))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_135))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.77/1.83  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.77/1.83  tff(c_331, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.77/1.83  tff(c_339, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_331])).
% 4.77/1.83  tff(c_354, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_339])).
% 4.77/1.83  tff(c_355, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_354])).
% 4.77/1.83  tff(c_513, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_495, c_355])).
% 4.77/1.83  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_513])).
% 4.77/1.83  tff(c_559, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_354])).
% 4.77/1.83  tff(c_936, plain, (![A_171, B_172, C_173, D_174]: (k2_relset_1(A_171, B_172, C_173)=B_172 | ~r2_relset_1(B_172, B_172, k1_partfun1(B_172, A_171, A_171, B_172, D_174, C_173), k6_partfun1(B_172)) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_172, A_171))) | ~v1_funct_2(D_174, B_172, A_171) | ~v1_funct_1(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.77/1.83  tff(c_942, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_559, c_936])).
% 4.77/1.83  tff(c_946, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_171, c_219, c_942])).
% 4.77/1.83  tff(c_948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_946])).
% 4.77/1.83  tff(c_950, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_589])).
% 4.77/1.83  tff(c_77, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 4.77/1.83  tff(c_954, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_950, c_77])).
% 4.77/1.83  tff(c_958, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_280, c_954])).
% 4.77/1.83  tff(c_966, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_958])).
% 4.77/1.83  tff(c_12, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.77/1.83  tff(c_78, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 4.77/1.83  tff(c_1042, plain, (![A_191, C_193, F_192, D_195, B_196, E_194]: (k1_partfun1(A_191, B_196, C_193, D_195, E_194, F_192)=k5_relat_1(E_194, F_192) | ~m1_subset_1(F_192, k1_zfmisc_1(k2_zfmisc_1(C_193, D_195))) | ~v1_funct_1(F_192) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_191, B_196))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.77/1.83  tff(c_1048, plain, (![A_191, B_196, E_194]: (k1_partfun1(A_191, B_196, '#skF_2', '#skF_1', E_194, '#skF_4')=k5_relat_1(E_194, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_191, B_196))) | ~v1_funct_1(E_194))), inference(resolution, [status(thm)], [c_66, c_1042])).
% 4.77/1.83  tff(c_1331, plain, (![A_212, B_213, E_214]: (k1_partfun1(A_212, B_213, '#skF_2', '#skF_1', E_214, '#skF_4')=k5_relat_1(E_214, '#skF_4') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_1(E_214))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1048])).
% 4.77/1.83  tff(c_1346, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1331])).
% 4.77/1.83  tff(c_1360, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_559, c_1346])).
% 4.77/1.83  tff(c_14, plain, (![A_9, B_11]: (v2_funct_1(A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(k5_relat_1(B_11, A_9)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.83  tff(c_1370, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1360, c_14])).
% 4.77/1.83  tff(c_1376, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_130, c_76, c_78, c_218, c_280, c_1370])).
% 4.77/1.83  tff(c_1378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_966, c_1376])).
% 4.77/1.83  tff(c_1396, plain, (![B_215]: (k2_funct_1('#skF_4')=B_215 | k5_relat_1(B_215, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_215)!='#skF_2' | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(splitRight, [status(thm)], [c_958])).
% 4.77/1.83  tff(c_1402, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_1396])).
% 4.77/1.83  tff(c_1414, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_218, c_1402])).
% 4.77/1.83  tff(c_1425, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1414])).
% 4.77/1.83  tff(c_1506, plain, (![B_237, C_234, A_232, E_235, D_236, F_233]: (k1_partfun1(A_232, B_237, C_234, D_236, E_235, F_233)=k5_relat_1(E_235, F_233) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(C_234, D_236))) | ~v1_funct_1(F_233) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_232, B_237))) | ~v1_funct_1(E_235))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.77/1.83  tff(c_1512, plain, (![A_232, B_237, E_235]: (k1_partfun1(A_232, B_237, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_232, B_237))) | ~v1_funct_1(E_235))), inference(resolution, [status(thm)], [c_66, c_1506])).
% 4.77/1.83  tff(c_1796, plain, (![A_252, B_253, E_254]: (k1_partfun1(A_252, B_253, '#skF_2', '#skF_1', E_254, '#skF_4')=k5_relat_1(E_254, '#skF_4') | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~v1_funct_1(E_254))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1512])).
% 4.77/1.83  tff(c_1811, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1796])).
% 4.77/1.83  tff(c_1825, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_559, c_1811])).
% 4.77/1.83  tff(c_1827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1425, c_1825])).
% 4.77/1.83  tff(c_1828, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1414])).
% 4.77/1.83  tff(c_1380, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_958])).
% 4.77/1.83  tff(c_8, plain, (![A_7]: (k4_relat_1(A_7)=k2_funct_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.83  tff(c_1383, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1380, c_8])).
% 4.77/1.83  tff(c_1386, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_1383])).
% 4.77/1.83  tff(c_1832, plain, (k4_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1828, c_1386])).
% 4.77/1.83  tff(c_6, plain, (![A_6]: (k4_relat_1(k4_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.77/1.83  tff(c_1840, plain, (k4_relat_1('#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1832, c_6])).
% 4.77/1.83  tff(c_1844, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_146, c_1840])).
% 4.77/1.83  tff(c_1846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1844])).
% 4.77/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.83  
% 4.77/1.83  Inference rules
% 4.77/1.83  ----------------------
% 4.77/1.83  #Ref     : 0
% 4.77/1.83  #Sup     : 387
% 4.77/1.83  #Fact    : 0
% 4.77/1.83  #Define  : 0
% 4.77/1.83  #Split   : 17
% 4.77/1.83  #Chain   : 0
% 4.77/1.83  #Close   : 0
% 4.77/1.83  
% 4.77/1.83  Ordering : KBO
% 4.77/1.83  
% 4.77/1.83  Simplification rules
% 4.77/1.83  ----------------------
% 4.77/1.83  #Subsume      : 2
% 4.77/1.83  #Demod        : 292
% 4.77/1.83  #Tautology    : 118
% 4.77/1.83  #SimpNegUnit  : 24
% 4.77/1.83  #BackRed      : 17
% 4.77/1.83  
% 4.77/1.83  #Partial instantiations: 0
% 4.77/1.83  #Strategies tried      : 1
% 4.77/1.83  
% 4.77/1.83  Timing (in seconds)
% 4.77/1.83  ----------------------
% 4.77/1.84  Preprocessing        : 0.36
% 4.77/1.84  Parsing              : 0.19
% 4.77/1.84  CNF conversion       : 0.03
% 4.77/1.84  Main loop            : 0.68
% 4.77/1.84  Inferencing          : 0.25
% 4.77/1.84  Reduction            : 0.23
% 4.77/1.84  Demodulation         : 0.16
% 4.77/1.84  BG Simplification    : 0.03
% 4.77/1.84  Subsumption          : 0.11
% 4.77/1.84  Abstraction          : 0.03
% 4.77/1.84  MUC search           : 0.00
% 4.77/1.84  Cooper               : 0.00
% 4.77/1.84  Total                : 1.10
% 4.77/1.84  Index Insertion      : 0.00
% 4.77/1.84  Index Deletion       : 0.00
% 4.90/1.84  Index Matching       : 0.00
% 4.90/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
