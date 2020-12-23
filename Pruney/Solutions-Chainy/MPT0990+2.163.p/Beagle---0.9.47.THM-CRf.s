%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:20 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  146 (1340 expanded)
%              Number of leaves         :   46 ( 489 expanded)
%              Depth                    :   23
%              Number of atoms          :  329 (5206 expanded)
%              Number of equality atoms :  124 (1884 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_193,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_150,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_102,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_167,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_109,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_109])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_204,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k8_relset_1(A_73,B_74,C_75,D_76) = k10_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,(
    ! [D_76] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_76) = k10_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_68,c_204])).

tff(c_286,plain,(
    ! [A_89,B_90,C_91] :
      ( k8_relset_1(A_89,B_90,C_91,B_90) = k1_relset_1(A_89,B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_292,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_4','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_286])).

tff(c_298,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k10_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_292])).

tff(c_340,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_349,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_340])).

tff(c_358,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_298,c_349])).

tff(c_359,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_358])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_115,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_155,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_161,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_155])).

tff(c_167,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_161])).

tff(c_6,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_6])).

tff(c_176,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_172])).

tff(c_212,plain,(
    ! [D_76] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_76) = k10_relat_1('#skF_3',D_76) ),
    inference(resolution,[status(thm)],[c_74,c_204])).

tff(c_290,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_286])).

tff(c_296,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_212,c_290])).

tff(c_346,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_340])).

tff(c_354,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_296,c_346])).

tff(c_355,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_354])).

tff(c_52,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_602,plain,(
    ! [A_144,B_145] :
      ( k2_funct_1(A_144) = B_145
      | k6_partfun1(k2_relat_1(A_144)) != k5_relat_1(B_145,A_144)
      | k2_relat_1(B_145) != k1_relat_1(A_144)
      | ~ v2_funct_1(A_144)
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_604,plain,(
    ! [B_145] :
      ( k2_funct_1('#skF_3') = B_145
      | k5_relat_1(B_145,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_145) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_602])).

tff(c_607,plain,(
    ! [B_146] :
      ( k2_funct_1('#skF_3') = B_146
      | k5_relat_1(B_146,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_146) != '#skF_1'
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_78,c_62,c_355,c_604])).

tff(c_610,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_607])).

tff(c_622,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_610])).

tff(c_623,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_622])).

tff(c_629,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_623])).

tff(c_28,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_79,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_145,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_152,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_79,c_145])).

tff(c_168,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_155])).

tff(c_532,plain,(
    ! [C_140,F_141,B_143,A_138,D_142,E_139] :
      ( m1_subset_1(k1_partfun1(A_138,B_143,C_140,D_142,E_139,F_141),k1_zfmisc_1(k2_zfmisc_1(A_138,D_142)))
      | ~ m1_subset_1(F_141,k1_zfmisc_1(k2_zfmisc_1(C_140,D_142)))
      | ~ v1_funct_1(F_141)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_143)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_390,plain,(
    ! [D_105,C_106,A_107,B_108] :
      ( D_105 = C_106
      | ~ r2_relset_1(A_107,B_108,C_106,D_105)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_398,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_390])).

tff(c_413,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_398])).

tff(c_414,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_548,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_532,c_414])).

tff(c_592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_548])).

tff(c_593,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_977,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_relset_1(A_178,B_179,C_180) = B_179
      | ~ r2_relset_1(B_179,B_179,k1_partfun1(B_179,A_178,A_178,B_179,D_181,C_180),k6_partfun1(B_179))
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(B_179,A_178)))
      | ~ v1_funct_2(D_181,B_179,A_178)
      | ~ v1_funct_1(D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_2(C_180,A_178,B_179)
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_980,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_977])).

tff(c_982,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_152,c_168,c_980])).

tff(c_984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_982])).

tff(c_986,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_623])).

tff(c_994,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_6])).

tff(c_1000,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_359,c_994])).

tff(c_80,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_partfun1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_991,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_80])).

tff(c_998,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_991])).

tff(c_1016,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_998])).

tff(c_1017,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1016])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_1072,plain,(
    ! [E_201,D_199,C_198,B_197,A_196,F_200] :
      ( k1_partfun1(A_196,B_197,C_198,D_199,E_201,F_200) = k5_relat_1(E_201,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_198,D_199)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1078,plain,(
    ! [A_196,B_197,E_201] :
      ( k1_partfun1(A_196,B_197,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_201) ) ),
    inference(resolution,[status(thm)],[c_68,c_1072])).

tff(c_1444,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_2','#skF_1',E_219,'#skF_4') = k5_relat_1(E_219,'#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1078])).

tff(c_1462,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1444])).

tff(c_1479,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_593,c_1462])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( v2_funct_1(A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(k5_relat_1(B_10,A_8))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1489,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_12])).

tff(c_1495,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_124,c_78,c_81,c_1000,c_167,c_1489])).

tff(c_1497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1017,c_1495])).

tff(c_1499,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1016])).

tff(c_1500,plain,(
    ! [B_220] :
      ( k2_funct_1('#skF_4') = B_220
      | k5_relat_1(B_220,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_220) != '#skF_2'
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(splitRight,[status(thm)],[c_1016])).

tff(c_1506,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_1500])).

tff(c_1518,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_167,c_1506])).

tff(c_1521,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1518])).

tff(c_1539,plain,(
    ! [F_236,C_234,B_233,A_232,E_237,D_235] :
      ( k1_partfun1(A_232,B_233,C_234,D_235,E_237,F_236) = k5_relat_1(E_237,F_236)
      | ~ m1_subset_1(F_236,k1_zfmisc_1(k2_zfmisc_1(C_234,D_235)))
      | ~ v1_funct_1(F_236)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1545,plain,(
    ! [A_232,B_233,E_237] :
      ( k1_partfun1(A_232,B_233,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_68,c_1539])).

tff(c_1877,plain,(
    ! [A_259,B_260,E_261] :
      ( k1_partfun1(A_259,B_260,'#skF_2','#skF_1',E_261,'#skF_4') = k5_relat_1(E_261,'#skF_4')
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(E_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1545])).

tff(c_1892,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1877])).

tff(c_1906,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_593,c_1892])).

tff(c_1908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1521,c_1906])).

tff(c_1909,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_18,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1915,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1909,c_18])).

tff(c_1919,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_1499,c_1915])).

tff(c_1921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.81  
% 4.59/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.81  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.59/1.81  
% 4.59/1.81  %Foreground sorts:
% 4.59/1.81  
% 4.59/1.81  
% 4.59/1.81  %Background operators:
% 4.59/1.81  
% 4.59/1.81  
% 4.59/1.81  %Foreground operators:
% 4.59/1.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.59/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.59/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.59/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.59/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.59/1.81  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.59/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.59/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.59/1.81  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.59/1.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.59/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.59/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.59/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.59/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.59/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.59/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.59/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.59/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.59/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.59/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.59/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.59/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.81  
% 4.59/1.84  tff(f_193, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.59/1.84  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.59/1.84  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.59/1.84  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.59/1.84  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.59/1.84  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.59/1.84  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.59/1.84  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.59/1.84  tff(f_150, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.59/1.84  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.59/1.84  tff(f_102, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.59/1.84  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.59/1.84  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.59/1.84  tff(f_167, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.59/1.84  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.59/1.84  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.59/1.84  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.59/1.84  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.59/1.84  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.59/1.84  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_109, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.84  tff(c_118, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_109])).
% 4.59/1.84  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_118])).
% 4.59/1.84  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_204, plain, (![A_73, B_74, C_75, D_76]: (k8_relset_1(A_73, B_74, C_75, D_76)=k10_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.59/1.84  tff(c_213, plain, (![D_76]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_76)=k10_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_68, c_204])).
% 4.59/1.84  tff(c_286, plain, (![A_89, B_90, C_91]: (k8_relset_1(A_89, B_90, C_91, B_90)=k1_relset_1(A_89, B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.59/1.84  tff(c_292, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_286])).
% 4.59/1.84  tff(c_298, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k10_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_292])).
% 4.59/1.84  tff(c_340, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.59/1.84  tff(c_349, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_340])).
% 4.59/1.84  tff(c_358, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_298, c_349])).
% 4.59/1.84  tff(c_359, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_358])).
% 4.59/1.84  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_115, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_109])).
% 4.59/1.84  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_115])).
% 4.59/1.84  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_155, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.59/1.84  tff(c_161, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_155])).
% 4.59/1.84  tff(c_167, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_161])).
% 4.59/1.84  tff(c_6, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.84  tff(c_172, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_167, c_6])).
% 4.59/1.84  tff(c_176, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_172])).
% 4.59/1.84  tff(c_212, plain, (![D_76]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_76)=k10_relat_1('#skF_3', D_76))), inference(resolution, [status(thm)], [c_74, c_204])).
% 4.59/1.84  tff(c_290, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_286])).
% 4.59/1.84  tff(c_296, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_212, c_290])).
% 4.59/1.84  tff(c_346, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_340])).
% 4.59/1.84  tff(c_354, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_296, c_346])).
% 4.59/1.84  tff(c_355, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_354])).
% 4.59/1.84  tff(c_52, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.59/1.84  tff(c_16, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.59/1.84  tff(c_602, plain, (![A_144, B_145]: (k2_funct_1(A_144)=B_145 | k6_partfun1(k2_relat_1(A_144))!=k5_relat_1(B_145, A_144) | k2_relat_1(B_145)!=k1_relat_1(A_144) | ~v2_funct_1(A_144) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 4.59/1.84  tff(c_604, plain, (![B_145]: (k2_funct_1('#skF_3')=B_145 | k5_relat_1(B_145, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_145)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_145) | ~v1_relat_1(B_145) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_602])).
% 4.59/1.84  tff(c_607, plain, (![B_146]: (k2_funct_1('#skF_3')=B_146 | k5_relat_1(B_146, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_146)!='#skF_1' | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_78, c_62, c_355, c_604])).
% 4.59/1.84  tff(c_610, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_127, c_607])).
% 4.59/1.84  tff(c_622, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_610])).
% 4.59/1.84  tff(c_623, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_622])).
% 4.59/1.84  tff(c_629, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_623])).
% 4.59/1.84  tff(c_28, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.59/1.84  tff(c_79, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 4.59/1.84  tff(c_145, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.59/1.84  tff(c_152, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_79, c_145])).
% 4.59/1.84  tff(c_168, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_155])).
% 4.59/1.84  tff(c_532, plain, (![C_140, F_141, B_143, A_138, D_142, E_139]: (m1_subset_1(k1_partfun1(A_138, B_143, C_140, D_142, E_139, F_141), k1_zfmisc_1(k2_zfmisc_1(A_138, D_142))) | ~m1_subset_1(F_141, k1_zfmisc_1(k2_zfmisc_1(C_140, D_142))) | ~v1_funct_1(F_141) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_143))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.59/1.84  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.59/1.84  tff(c_390, plain, (![D_105, C_106, A_107, B_108]: (D_105=C_106 | ~r2_relset_1(A_107, B_108, C_106, D_105) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.59/1.84  tff(c_398, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_390])).
% 4.59/1.84  tff(c_413, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_398])).
% 4.59/1.84  tff(c_414, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_413])).
% 4.59/1.84  tff(c_548, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_532, c_414])).
% 4.59/1.84  tff(c_592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_548])).
% 4.59/1.84  tff(c_593, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_413])).
% 4.59/1.84  tff(c_977, plain, (![A_178, B_179, C_180, D_181]: (k2_relset_1(A_178, B_179, C_180)=B_179 | ~r2_relset_1(B_179, B_179, k1_partfun1(B_179, A_178, A_178, B_179, D_181, C_180), k6_partfun1(B_179)) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(B_179, A_178))) | ~v1_funct_2(D_181, B_179, A_178) | ~v1_funct_1(D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_2(C_180, A_178, B_179) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.59/1.84  tff(c_980, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_593, c_977])).
% 4.59/1.84  tff(c_982, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_152, c_168, c_980])).
% 4.59/1.84  tff(c_984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_982])).
% 4.59/1.84  tff(c_986, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_623])).
% 4.59/1.84  tff(c_994, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_986, c_6])).
% 4.59/1.84  tff(c_1000, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_359, c_994])).
% 4.59/1.84  tff(c_80, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_partfun1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 4.59/1.84  tff(c_991, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_986, c_80])).
% 4.59/1.84  tff(c_998, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_991])).
% 4.59/1.84  tff(c_1016, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_998])).
% 4.59/1.84  tff(c_1017, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1016])).
% 4.59/1.84  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.59/1.84  tff(c_81, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 4.59/1.84  tff(c_1072, plain, (![E_201, D_199, C_198, B_197, A_196, F_200]: (k1_partfun1(A_196, B_197, C_198, D_199, E_201, F_200)=k5_relat_1(E_201, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_198, D_199))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_201))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.84  tff(c_1078, plain, (![A_196, B_197, E_201]: (k1_partfun1(A_196, B_197, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_201))), inference(resolution, [status(thm)], [c_68, c_1072])).
% 4.59/1.84  tff(c_1444, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_2', '#skF_1', E_219, '#skF_4')=k5_relat_1(E_219, '#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1078])).
% 4.59/1.84  tff(c_1462, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1444])).
% 4.59/1.84  tff(c_1479, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_593, c_1462])).
% 4.59/1.84  tff(c_12, plain, (![A_8, B_10]: (v2_funct_1(A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(k5_relat_1(B_10, A_8)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.59/1.84  tff(c_1489, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1479, c_12])).
% 4.59/1.84  tff(c_1495, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_124, c_78, c_81, c_1000, c_167, c_1489])).
% 4.59/1.84  tff(c_1497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1017, c_1495])).
% 4.59/1.84  tff(c_1499, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1016])).
% 4.59/1.84  tff(c_1500, plain, (![B_220]: (k2_funct_1('#skF_4')=B_220 | k5_relat_1(B_220, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_220)!='#skF_2' | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(splitRight, [status(thm)], [c_1016])).
% 4.59/1.84  tff(c_1506, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_1500])).
% 4.59/1.84  tff(c_1518, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_167, c_1506])).
% 4.59/1.84  tff(c_1521, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1518])).
% 4.59/1.84  tff(c_1539, plain, (![F_236, C_234, B_233, A_232, E_237, D_235]: (k1_partfun1(A_232, B_233, C_234, D_235, E_237, F_236)=k5_relat_1(E_237, F_236) | ~m1_subset_1(F_236, k1_zfmisc_1(k2_zfmisc_1(C_234, D_235))) | ~v1_funct_1(F_236) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.59/1.84  tff(c_1545, plain, (![A_232, B_233, E_237]: (k1_partfun1(A_232, B_233, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_68, c_1539])).
% 4.59/1.84  tff(c_1877, plain, (![A_259, B_260, E_261]: (k1_partfun1(A_259, B_260, '#skF_2', '#skF_1', E_261, '#skF_4')=k5_relat_1(E_261, '#skF_4') | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(E_261))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1545])).
% 4.59/1.84  tff(c_1892, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1877])).
% 4.59/1.84  tff(c_1906, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_593, c_1892])).
% 4.59/1.84  tff(c_1908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1521, c_1906])).
% 4.59/1.84  tff(c_1909, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1518])).
% 4.59/1.84  tff(c_18, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.59/1.84  tff(c_1915, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1909, c_18])).
% 4.59/1.84  tff(c_1919, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_1499, c_1915])).
% 4.59/1.84  tff(c_1921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1919])).
% 4.59/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.84  
% 4.59/1.84  Inference rules
% 4.59/1.84  ----------------------
% 4.59/1.84  #Ref     : 0
% 4.59/1.84  #Sup     : 404
% 4.59/1.84  #Fact    : 0
% 4.59/1.84  #Define  : 0
% 4.59/1.84  #Split   : 18
% 4.59/1.84  #Chain   : 0
% 4.59/1.84  #Close   : 0
% 4.59/1.84  
% 4.59/1.84  Ordering : KBO
% 4.59/1.84  
% 4.59/1.84  Simplification rules
% 4.59/1.84  ----------------------
% 4.59/1.84  #Subsume      : 2
% 4.59/1.84  #Demod        : 302
% 4.59/1.84  #Tautology    : 104
% 4.59/1.84  #SimpNegUnit  : 25
% 4.59/1.84  #BackRed      : 14
% 4.59/1.84  
% 4.59/1.84  #Partial instantiations: 0
% 4.59/1.84  #Strategies tried      : 1
% 4.59/1.84  
% 4.59/1.84  Timing (in seconds)
% 4.59/1.84  ----------------------
% 4.59/1.84  Preprocessing        : 0.39
% 4.59/1.84  Parsing              : 0.22
% 4.59/1.84  CNF conversion       : 0.03
% 4.59/1.84  Main loop            : 0.63
% 4.59/1.84  Inferencing          : 0.22
% 4.59/1.84  Reduction            : 0.21
% 4.59/1.84  Demodulation         : 0.15
% 4.59/1.84  BG Simplification    : 0.03
% 4.59/1.84  Subsumption          : 0.11
% 4.59/1.84  Abstraction          : 0.03
% 4.59/1.84  MUC search           : 0.00
% 4.59/1.84  Cooper               : 0.00
% 4.59/1.84  Total                : 1.07
% 4.59/1.84  Index Insertion      : 0.00
% 4.59/1.84  Index Deletion       : 0.00
% 4.59/1.84  Index Matching       : 0.00
% 4.59/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
