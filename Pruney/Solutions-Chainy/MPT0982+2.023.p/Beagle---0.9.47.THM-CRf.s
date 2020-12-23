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
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 266 expanded)
%              Number of leaves         :   48 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  228 ( 826 expanded)
%              Number of equality atoms :   76 ( 252 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_396,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_408,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_396])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_415,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_54])).

tff(c_136,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_424,plain,(
    ! [A_113,B_114,C_115] :
      ( m1_subset_1(k2_relset_1(A_113,B_114,C_115),k1_zfmisc_1(B_114))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_453,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_424])).

tff(c_466,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_453])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_481,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_466,c_10])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_149,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_325,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_338,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_325])).

tff(c_2462,plain,(
    ! [B_301,A_302,C_303] :
      ( k1_xboole_0 = B_301
      | k1_relset_1(A_302,B_301,C_303) = A_302
      | ~ v1_funct_2(C_303,A_302,B_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2479,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2462])).

tff(c_2490,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_338,c_2479])).

tff(c_2491,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2490])).

tff(c_409,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_396])).

tff(c_450,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_424])).

tff(c_464,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_450])).

tff(c_470,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_464,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_477,plain,(
    k3_xboole_0(k2_relat_1('#skF_5'),'#skF_3') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_470,c_8])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,k3_xboole_0(k2_relat_1(B_13),A_12)) = k10_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_505,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_18])).

tff(c_509,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_505])).

tff(c_168,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_181,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_168])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_190,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_20])).

tff(c_193,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_190])).

tff(c_267,plain,(
    ! [B_93,A_94] :
      ( k2_relat_1(k7_relat_1(B_93,A_94)) = k9_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_279,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_267])).

tff(c_288,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_279])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2363,plain,(
    ! [B_284,A_285] :
      ( k10_relat_1(B_284,k9_relat_1(B_284,A_285)) = A_285
      | ~ v2_funct_1(B_284)
      | ~ r1_tarski(A_285,k1_relat_1(B_284))
      | ~ v1_funct_1(B_284)
      | ~ v1_relat_1(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2375,plain,(
    ! [B_284] :
      ( k10_relat_1(B_284,k9_relat_1(B_284,k1_relat_1(B_284))) = k1_relat_1(B_284)
      | ~ v2_funct_1(B_284)
      | ~ v1_funct_1(B_284)
      | ~ v1_relat_1(B_284) ) ),
    inference(resolution,[status(thm)],[c_6,c_2363])).

tff(c_2496,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_2375])).

tff(c_2502,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_66,c_58,c_2491,c_509,c_288,c_2496])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3154,plain,(
    ! [A_350,B_349,F_347,D_348,E_352,C_351] :
      ( k1_partfun1(A_350,B_349,C_351,D_348,E_352,F_347) = k5_relat_1(E_352,F_347)
      | ~ m1_subset_1(F_347,k1_zfmisc_1(k2_zfmisc_1(C_351,D_348)))
      | ~ v1_funct_1(F_347)
      | ~ m1_subset_1(E_352,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349)))
      | ~ v1_funct_1(E_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3175,plain,(
    ! [A_350,B_349,E_352] :
      ( k1_partfun1(A_350,B_349,'#skF_2','#skF_3',E_352,'#skF_5') = k5_relat_1(E_352,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_352,k1_zfmisc_1(k2_zfmisc_1(A_350,B_349)))
      | ~ v1_funct_1(E_352) ) ),
    inference(resolution,[status(thm)],[c_62,c_3154])).

tff(c_3935,plain,(
    ! [A_373,B_374,E_375] :
      ( k1_partfun1(A_373,B_374,'#skF_2','#skF_3',E_375,'#skF_5') = k5_relat_1(E_375,'#skF_5')
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ v1_funct_1(E_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3175])).

tff(c_3968,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3935])).

tff(c_3983,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3968])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_997,plain,(
    ! [F_188,B_185,D_187,E_189,C_186,A_184] :
      ( k4_relset_1(A_184,B_185,C_186,D_187,E_189,F_188) = k5_relat_1(E_189,F_188)
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(C_186,D_187)))
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1309,plain,(
    ! [A_220,B_221,E_222] :
      ( k4_relset_1(A_220,B_221,'#skF_2','#skF_3',E_222,'#skF_5') = k5_relat_1(E_222,'#skF_5')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(resolution,[status(thm)],[c_62,c_997])).

tff(c_1339,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1309])).

tff(c_32,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k4_relset_1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1669,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_32])).

tff(c_1673,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_1669])).

tff(c_1727,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1673,c_10])).

tff(c_1427,plain,(
    ! [C_227,E_228,B_225,F_223,D_224,A_226] :
      ( k1_partfun1(A_226,B_225,C_227,D_224,E_228,F_223) = k5_relat_1(E_228,F_223)
      | ~ m1_subset_1(F_223,k1_zfmisc_1(k2_zfmisc_1(C_227,D_224)))
      | ~ v1_funct_1(F_223)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_1(E_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1446,plain,(
    ! [A_226,B_225,E_228] :
      ( k1_partfun1(A_226,B_225,'#skF_2','#skF_3',E_228,'#skF_5') = k5_relat_1(E_228,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_1(E_228) ) ),
    inference(resolution,[status(thm)],[c_62,c_1427])).

tff(c_1989,plain,(
    ! [A_243,B_244,E_245] :
      ( k1_partfun1(A_243,B_244,'#skF_2','#skF_3',E_245,'#skF_5') = k5_relat_1(E_245,'#skF_5')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1446])).

tff(c_2019,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1989])).

tff(c_2033,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2019])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_456,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_424])).

tff(c_521,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_642,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_521])).

tff(c_2037,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_642])).

tff(c_2042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1727,c_2037])).

tff(c_2044,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_36,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_relset_1(A_36,B_37,C_38) = k2_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2052,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2044,c_36])).

tff(c_2069,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2052])).

tff(c_3994,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_2069])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( k9_relat_1(B_11,k2_relat_1(A_9)) = k2_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k9_relat_1(B_17,A_16)) = A_16
      | ~ v2_funct_1(B_17)
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2498,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_16)) = A_16
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_16,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_22])).

tff(c_2570,plain,(
    ! [A_307] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_307)) = A_307
      | ~ r1_tarski(A_307,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_66,c_58,c_2498])).

tff(c_2588,plain,(
    ! [A_9] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5'))) = k2_relat_1(A_9)
      | ~ r1_tarski(k2_relat_1(A_9),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2570])).

tff(c_2599,plain,(
    ! [A_9] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5'))) = k2_relat_1(A_9)
      | ~ r1_tarski(k2_relat_1(A_9),'#skF_2')
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2588])).

tff(c_4017,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3994,c_2599])).

tff(c_4030,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_481,c_2502,c_4017])).

tff(c_4032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_4030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.22  
% 5.84/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.22  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.84/2.22  
% 5.84/2.22  %Foreground sorts:
% 5.84/2.22  
% 5.84/2.22  
% 5.84/2.22  %Background operators:
% 5.84/2.22  
% 5.84/2.22  
% 5.84/2.22  %Foreground operators:
% 5.84/2.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.84/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.84/2.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.84/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.84/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.84/2.22  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.84/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.84/2.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.84/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.84/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.84/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.84/2.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.84/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.22  tff('#skF_1', type, '#skF_1': $i).
% 5.84/2.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.84/2.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.84/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.84/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.84/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.84/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.84/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.84/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.84/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.22  
% 6.20/2.24  tff(f_154, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 6.20/2.24  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.20/2.24  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.20/2.24  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.20/2.24  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.20/2.24  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.20/2.24  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.20/2.24  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.20/2.24  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 6.20/2.24  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.20/2.24  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.20/2.24  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.20/2.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.20/2.24  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 6.20/2.24  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.20/2.24  tff(f_104, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 6.20/2.24  tff(f_90, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 6.20/2.24  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 6.20/2.24  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_396, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.20/2.24  tff(c_408, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_396])).
% 6.20/2.24  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_415, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_54])).
% 6.20/2.24  tff(c_136, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.20/2.24  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_136])).
% 6.20/2.24  tff(c_424, plain, (![A_113, B_114, C_115]: (m1_subset_1(k2_relset_1(A_113, B_114, C_115), k1_zfmisc_1(B_114)) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.20/2.24  tff(c_453, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_408, c_424])).
% 6.20/2.24  tff(c_466, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_453])).
% 6.20/2.24  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.20/2.24  tff(c_481, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_466, c_10])).
% 6.20/2.24  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_149, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_136])).
% 6.20/2.24  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_58, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_325, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.20/2.24  tff(c_338, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_325])).
% 6.20/2.24  tff(c_2462, plain, (![B_301, A_302, C_303]: (k1_xboole_0=B_301 | k1_relset_1(A_302, B_301, C_303)=A_302 | ~v1_funct_2(C_303, A_302, B_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.20/2.24  tff(c_2479, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_2462])).
% 6.20/2.24  tff(c_2490, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_338, c_2479])).
% 6.20/2.24  tff(c_2491, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_2490])).
% 6.20/2.24  tff(c_409, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_396])).
% 6.20/2.24  tff(c_450, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_409, c_424])).
% 6.20/2.24  tff(c_464, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_450])).
% 6.20/2.24  tff(c_470, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_464, c_10])).
% 6.20/2.24  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.20/2.24  tff(c_477, plain, (k3_xboole_0(k2_relat_1('#skF_5'), '#skF_3')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_470, c_8])).
% 6.20/2.24  tff(c_18, plain, (![B_13, A_12]: (k10_relat_1(B_13, k3_xboole_0(k2_relat_1(B_13), A_12))=k10_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.20/2.24  tff(c_505, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_477, c_18])).
% 6.20/2.24  tff(c_509, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_505])).
% 6.20/2.24  tff(c_168, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.20/2.24  tff(c_181, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_168])).
% 6.20/2.24  tff(c_20, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.20/2.24  tff(c_190, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_181, c_20])).
% 6.20/2.24  tff(c_193, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_190])).
% 6.20/2.24  tff(c_267, plain, (![B_93, A_94]: (k2_relat_1(k7_relat_1(B_93, A_94))=k9_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.20/2.24  tff(c_279, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_193, c_267])).
% 6.20/2.24  tff(c_288, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_279])).
% 6.20/2.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.20/2.24  tff(c_2363, plain, (![B_284, A_285]: (k10_relat_1(B_284, k9_relat_1(B_284, A_285))=A_285 | ~v2_funct_1(B_284) | ~r1_tarski(A_285, k1_relat_1(B_284)) | ~v1_funct_1(B_284) | ~v1_relat_1(B_284))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.20/2.24  tff(c_2375, plain, (![B_284]: (k10_relat_1(B_284, k9_relat_1(B_284, k1_relat_1(B_284)))=k1_relat_1(B_284) | ~v2_funct_1(B_284) | ~v1_funct_1(B_284) | ~v1_relat_1(B_284))), inference(resolution, [status(thm)], [c_6, c_2363])).
% 6.20/2.24  tff(c_2496, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2491, c_2375])).
% 6.20/2.24  tff(c_2502, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_66, c_58, c_2491, c_509, c_288, c_2496])).
% 6.20/2.24  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_3154, plain, (![A_350, B_349, F_347, D_348, E_352, C_351]: (k1_partfun1(A_350, B_349, C_351, D_348, E_352, F_347)=k5_relat_1(E_352, F_347) | ~m1_subset_1(F_347, k1_zfmisc_1(k2_zfmisc_1(C_351, D_348))) | ~v1_funct_1(F_347) | ~m1_subset_1(E_352, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))) | ~v1_funct_1(E_352))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.20/2.24  tff(c_3175, plain, (![A_350, B_349, E_352]: (k1_partfun1(A_350, B_349, '#skF_2', '#skF_3', E_352, '#skF_5')=k5_relat_1(E_352, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_352, k1_zfmisc_1(k2_zfmisc_1(A_350, B_349))) | ~v1_funct_1(E_352))), inference(resolution, [status(thm)], [c_62, c_3154])).
% 6.20/2.24  tff(c_3935, plain, (![A_373, B_374, E_375]: (k1_partfun1(A_373, B_374, '#skF_2', '#skF_3', E_375, '#skF_5')=k5_relat_1(E_375, '#skF_5') | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~v1_funct_1(E_375))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3175])).
% 6.20/2.24  tff(c_3968, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_3935])).
% 6.20/2.24  tff(c_3983, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3968])).
% 6.20/2.24  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.20/2.24  tff(c_997, plain, (![F_188, B_185, D_187, E_189, C_186, A_184]: (k4_relset_1(A_184, B_185, C_186, D_187, E_189, F_188)=k5_relat_1(E_189, F_188) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(C_186, D_187))) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.20/2.24  tff(c_1309, plain, (![A_220, B_221, E_222]: (k4_relset_1(A_220, B_221, '#skF_2', '#skF_3', E_222, '#skF_5')=k5_relat_1(E_222, '#skF_5') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(resolution, [status(thm)], [c_62, c_997])).
% 6.20/2.24  tff(c_1339, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_1309])).
% 6.20/2.24  tff(c_32, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k4_relset_1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.20/2.24  tff(c_1669, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_32])).
% 6.20/2.24  tff(c_1673, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_1669])).
% 6.20/2.24  tff(c_1727, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_1673, c_10])).
% 6.20/2.24  tff(c_1427, plain, (![C_227, E_228, B_225, F_223, D_224, A_226]: (k1_partfun1(A_226, B_225, C_227, D_224, E_228, F_223)=k5_relat_1(E_228, F_223) | ~m1_subset_1(F_223, k1_zfmisc_1(k2_zfmisc_1(C_227, D_224))) | ~v1_funct_1(F_223) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_1(E_228))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.20/2.24  tff(c_1446, plain, (![A_226, B_225, E_228]: (k1_partfun1(A_226, B_225, '#skF_2', '#skF_3', E_228, '#skF_5')=k5_relat_1(E_228, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_1(E_228))), inference(resolution, [status(thm)], [c_62, c_1427])).
% 6.20/2.24  tff(c_1989, plain, (![A_243, B_244, E_245]: (k1_partfun1(A_243, B_244, '#skF_2', '#skF_3', E_245, '#skF_5')=k5_relat_1(E_245, '#skF_5') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(E_245))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1446])).
% 6.20/2.24  tff(c_2019, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1989])).
% 6.20/2.24  tff(c_2033, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2019])).
% 6.20/2.24  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.20/2.24  tff(c_456, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_424])).
% 6.20/2.24  tff(c_521, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_456])).
% 6.20/2.24  tff(c_642, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_521])).
% 6.20/2.24  tff(c_2037, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_642])).
% 6.20/2.24  tff(c_2042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1727, c_2037])).
% 6.20/2.24  tff(c_2044, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_456])).
% 6.20/2.24  tff(c_36, plain, (![A_36, B_37, C_38]: (k2_relset_1(A_36, B_37, C_38)=k2_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.20/2.24  tff(c_2052, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2044, c_36])).
% 6.20/2.24  tff(c_2069, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2052])).
% 6.20/2.24  tff(c_3994, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3983, c_2069])).
% 6.20/2.24  tff(c_16, plain, (![B_11, A_9]: (k9_relat_1(B_11, k2_relat_1(A_9))=k2_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.20/2.24  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k9_relat_1(B_17, A_16))=A_16 | ~v2_funct_1(B_17) | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.20/2.24  tff(c_2498, plain, (![A_16]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_16))=A_16 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_16, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2491, c_22])).
% 6.20/2.24  tff(c_2570, plain, (![A_307]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_307))=A_307 | ~r1_tarski(A_307, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_66, c_58, c_2498])).
% 6.20/2.24  tff(c_2588, plain, (![A_9]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5')))=k2_relat_1(A_9) | ~r1_tarski(k2_relat_1(A_9), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2570])).
% 6.20/2.24  tff(c_2599, plain, (![A_9]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5')))=k2_relat_1(A_9) | ~r1_tarski(k2_relat_1(A_9), '#skF_2') | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2588])).
% 6.20/2.24  tff(c_4017, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3994, c_2599])).
% 6.20/2.24  tff(c_4030, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_481, c_2502, c_4017])).
% 6.20/2.24  tff(c_4032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_4030])).
% 6.20/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.20/2.24  
% 6.20/2.24  Inference rules
% 6.20/2.24  ----------------------
% 6.20/2.24  #Ref     : 0
% 6.20/2.24  #Sup     : 924
% 6.20/2.24  #Fact    : 0
% 6.20/2.24  #Define  : 0
% 6.20/2.24  #Split   : 13
% 6.20/2.24  #Chain   : 0
% 6.20/2.24  #Close   : 0
% 6.20/2.24  
% 6.20/2.24  Ordering : KBO
% 6.20/2.24  
% 6.20/2.24  Simplification rules
% 6.20/2.24  ----------------------
% 6.20/2.24  #Subsume      : 17
% 6.20/2.24  #Demod        : 378
% 6.20/2.24  #Tautology    : 331
% 6.20/2.24  #SimpNegUnit  : 34
% 6.20/2.24  #BackRed      : 34
% 6.20/2.24  
% 6.20/2.24  #Partial instantiations: 0
% 6.20/2.24  #Strategies tried      : 1
% 6.20/2.24  
% 6.20/2.24  Timing (in seconds)
% 6.20/2.24  ----------------------
% 6.20/2.25  Preprocessing        : 0.37
% 6.20/2.25  Parsing              : 0.20
% 6.20/2.25  CNF conversion       : 0.03
% 6.20/2.25  Main loop            : 1.09
% 6.20/2.25  Inferencing          : 0.36
% 6.20/2.25  Reduction            : 0.40
% 6.20/2.25  Demodulation         : 0.27
% 6.20/2.25  BG Simplification    : 0.04
% 6.20/2.25  Subsumption          : 0.19
% 6.20/2.25  Abstraction          : 0.05
% 6.20/2.25  MUC search           : 0.00
% 6.20/2.25  Cooper               : 0.00
% 6.20/2.25  Total                : 1.51
% 6.20/2.25  Index Insertion      : 0.00
% 6.20/2.25  Index Deletion       : 0.00
% 6.20/2.25  Index Matching       : 0.00
% 6.20/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
