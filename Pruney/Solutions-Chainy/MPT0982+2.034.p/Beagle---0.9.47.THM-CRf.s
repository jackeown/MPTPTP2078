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
% DateTime   : Thu Dec  3 10:12:00 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 442 expanded)
%              Number of leaves         :   50 ( 173 expanded)
%              Depth                    :   12
%              Number of atoms          :  278 (1314 expanded)
%              Number of equality atoms :   82 ( 339 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_301,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_313,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_301])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_315,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_64])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_113,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_122,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_113])).

tff(c_129,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_122])).

tff(c_435,plain,(
    ! [A_121,B_122,C_123] :
      ( m1_subset_1(k2_relset_1(A_121,B_122,C_123),k1_zfmisc_1(B_122))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_466,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_435])).

tff(c_479,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_466])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_502,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_479,c_8])).

tff(c_314,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_301])).

tff(c_463,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_435])).

tff(c_477,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_463])).

tff(c_487,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_477,c_8])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_374,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_387,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_374])).

tff(c_4666,plain,(
    ! [B_368,A_369,C_370] :
      ( k1_xboole_0 = B_368
      | k1_relset_1(A_369,B_368,C_370) = A_369
      | ~ v1_funct_2(C_370,A_369,B_368)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_369,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4690,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4666])).

tff(c_4703,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_387,c_4690])).

tff(c_4704,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4703])).

tff(c_160,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_173,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_160])).

tff(c_223,plain,(
    ! [B_96,A_97] :
      ( k7_relat_1(B_96,A_97) = B_96
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_173,c_223])).

tff(c_238,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_229])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_249,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_16])).

tff(c_253,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_249])).

tff(c_4993,plain,(
    ! [A_374,C_375,B_376] :
      ( r1_tarski(A_374,k10_relat_1(C_375,B_376))
      | ~ r1_tarski(k9_relat_1(C_375,A_374),B_376)
      | ~ r1_tarski(A_374,k1_relat_1(C_375))
      | ~ v1_funct_1(C_375)
      | ~ v1_relat_1(C_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5012,plain,(
    ! [B_376] :
      ( r1_tarski('#skF_2',k10_relat_1('#skF_5',B_376))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_376)
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_4993])).

tff(c_5705,plain,(
    ! [B_407] :
      ( r1_tarski('#skF_2',k10_relat_1('#skF_5',B_407))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_6,c_4704,c_5012])).

tff(c_5718,plain,(
    r1_tarski('#skF_2',k10_relat_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_487,c_5705])).

tff(c_512,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k8_relset_1(A_124,B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_598,plain,(
    ! [D_135] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_135) = k10_relat_1('#skF_5',D_135) ),
    inference(resolution,[status(thm)],[c_72,c_512])).

tff(c_34,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( m1_subset_1(k8_relset_1(A_34,B_35,C_36,D_37),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_604,plain,(
    ! [D_135] :
      ( m1_subset_1(k10_relat_1('#skF_5',D_135),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_34])).

tff(c_612,plain,(
    ! [D_136] : m1_subset_1(k10_relat_1('#skF_5',D_136),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_604])).

tff(c_621,plain,(
    ! [D_137] : r1_tarski(k10_relat_1('#skF_5',D_137),'#skF_2') ),
    inference(resolution,[status(thm)],[c_612,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_628,plain,(
    ! [D_137] :
      ( k10_relat_1('#skF_5',D_137) = '#skF_2'
      | ~ r1_tarski('#skF_2',k10_relat_1('#skF_5',D_137)) ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_5781,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_5718,c_628])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_5478,plain,(
    ! [B_397,C_402,F_399,E_398,A_400,D_401] :
      ( k1_partfun1(A_400,B_397,C_402,D_401,E_398,F_399) = k5_relat_1(E_398,F_399)
      | ~ m1_subset_1(F_399,k1_zfmisc_1(k2_zfmisc_1(C_402,D_401)))
      | ~ v1_funct_1(F_399)
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(A_400,B_397)))
      | ~ v1_funct_1(E_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5503,plain,(
    ! [A_400,B_397,E_398] :
      ( k1_partfun1(A_400,B_397,'#skF_2','#skF_3',E_398,'#skF_5') = k5_relat_1(E_398,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(A_400,B_397)))
      | ~ v1_funct_1(E_398) ) ),
    inference(resolution,[status(thm)],[c_72,c_5478])).

tff(c_7362,plain,(
    ! [A_460,B_461,E_462] :
      ( k1_partfun1(A_460,B_461,'#skF_2','#skF_3',E_462,'#skF_5') = k5_relat_1(E_462,'#skF_5')
      | ~ m1_subset_1(E_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ v1_funct_1(E_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5503])).

tff(c_7410,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_7362])).

tff(c_7434,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7410])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1474,plain,(
    ! [A_207,F_203,D_204,B_206,E_202,C_205] :
      ( k4_relset_1(A_207,B_206,C_205,D_204,E_202,F_203) = k5_relat_1(E_202,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_205,D_204)))
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2020,plain,(
    ! [A_230,B_231,E_232] :
      ( k4_relset_1(A_230,B_231,'#skF_2','#skF_3',E_232,'#skF_5') = k5_relat_1(E_232,'#skF_5')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(resolution,[status(thm)],[c_72,c_1474])).

tff(c_2066,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_2020])).

tff(c_32,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k4_relset_1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2389,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2066,c_32])).

tff(c_2393,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_2389])).

tff(c_2459,plain,(
    r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2393,c_8])).

tff(c_1779,plain,(
    ! [C_225,B_220,A_223,E_221,D_224,F_222] :
      ( k1_partfun1(A_223,B_220,C_225,D_224,E_221,F_222) = k5_relat_1(E_221,F_222)
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(C_225,D_224)))
      | ~ v1_funct_1(F_222)
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_220)))
      | ~ v1_funct_1(E_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1802,plain,(
    ! [A_223,B_220,E_221] :
      ( k1_partfun1(A_223,B_220,'#skF_2','#skF_3',E_221,'#skF_5') = k5_relat_1(E_221,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_220)))
      | ~ v1_funct_1(E_221) ) ),
    inference(resolution,[status(thm)],[c_72,c_1779])).

tff(c_4002,plain,(
    ! [A_309,B_310,E_311] :
      ( k1_partfun1(A_309,B_310,'#skF_2','#skF_3',E_311,'#skF_5') = k5_relat_1(E_311,'#skF_5')
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_1(E_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1802])).

tff(c_4050,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_4002])).

tff(c_4074,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4050])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_469,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_435])).

tff(c_684,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_839,plain,(
    ~ r1_tarski(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_684])).

tff(c_4110,plain,(
    ~ r1_tarski(k5_relat_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_839])).

tff(c_4115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_4110])).

tff(c_4117,plain,(
    m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_38,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4282,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4117,c_38])).

tff(c_4300,plain,(
    k2_relat_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4282])).

tff(c_7447,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7434,c_4300])).

tff(c_5118,plain,(
    ! [C_380,D_379,B_381,E_377,F_378,A_382] :
      ( k4_relset_1(A_382,B_381,C_380,D_379,E_377,F_378) = k5_relat_1(E_377,F_378)
      | ~ m1_subset_1(F_378,k1_zfmisc_1(k2_zfmisc_1(C_380,D_379)))
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(A_382,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5721,plain,(
    ! [A_408,B_409,E_410] :
      ( k4_relset_1(A_408,B_409,'#skF_2','#skF_3',E_410,'#skF_5') = k5_relat_1(E_410,'#skF_5')
      | ~ m1_subset_1(E_410,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409))) ) ),
    inference(resolution,[status(thm)],[c_72,c_5118])).

tff(c_5771,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_5721])).

tff(c_5894,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5771,c_32])).

tff(c_5898,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_5894])).

tff(c_5958,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_5898,c_38])).

tff(c_475,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(k2_relset_1(A_121,B_122,C_123),B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(resolution,[status(thm)],[c_435,c_8])).

tff(c_5955,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5898,c_475])).

tff(c_6533,plain,(
    r1_tarski(k2_relat_1(k5_relat_1('#skF_4','#skF_5')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5958,c_5955])).

tff(c_6554,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6533,c_2])).

tff(c_7124,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_6554])).

tff(c_7461,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7447,c_7124])).

tff(c_7468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7461])).

tff(c_7469,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6554])).

tff(c_119,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_113])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_172,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_160])).

tff(c_232,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_172,c_223])).

tff(c_241,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_232])).

tff(c_258,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_16])).

tff(c_262,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_258])).

tff(c_324,plain,(
    ! [B_107,A_108] :
      ( k9_relat_1(B_107,k2_relat_1(A_108)) = k2_relat_1(k5_relat_1(A_108,B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7964,plain,(
    ! [B_472,A_473,B_474] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_472,A_473),B_474)) = k9_relat_1(B_474,k9_relat_1(B_472,A_473))
      | ~ v1_relat_1(B_474)
      | ~ v1_relat_1(k7_relat_1(B_472,A_473))
      | ~ v1_relat_1(B_472) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_324])).

tff(c_8018,plain,(
    ! [B_474] :
      ( k9_relat_1(B_474,k9_relat_1('#skF_4','#skF_1')) = k2_relat_1(k5_relat_1('#skF_4',B_474))
      | ~ v1_relat_1(B_474)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_7964])).

tff(c_8038,plain,(
    ! [B_475] :
      ( k9_relat_1(B_475,k2_relat_1('#skF_4')) = k2_relat_1(k5_relat_1('#skF_4',B_475))
      | ~ v1_relat_1(B_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_241,c_262,c_8018])).

tff(c_68,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,A_20)) = A_20
      | ~ v2_funct_1(B_21)
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4711,plain,(
    ! [A_20] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_20)) = A_20
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4704,c_24])).

tff(c_4738,plain,(
    ! [A_20] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76,c_68,c_4711])).

tff(c_8048,plain,
    ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1('#skF_4','#skF_5'))) = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8038,c_4738])).

tff(c_8072,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_502,c_5781,c_7469,c_8048])).

tff(c_8074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_8072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.63/2.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.98  
% 7.78/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.98  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k8_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.78/2.98  
% 7.78/2.98  %Foreground sorts:
% 7.78/2.98  
% 7.78/2.98  
% 7.78/2.98  %Background operators:
% 7.78/2.98  
% 7.78/2.98  
% 7.78/2.98  %Foreground operators:
% 7.78/2.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.78/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.78/2.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.78/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.78/2.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.78/2.98  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.78/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.78/2.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.78/2.98  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.78/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.78/2.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.78/2.98  tff('#skF_5', type, '#skF_5': $i).
% 7.78/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.78/2.98  tff('#skF_2', type, '#skF_2': $i).
% 7.78/2.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.78/2.98  tff('#skF_3', type, '#skF_3': $i).
% 7.78/2.98  tff('#skF_1', type, '#skF_1': $i).
% 7.78/2.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.78/2.98  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.78/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.78/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.78/2.98  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.78/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.78/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.78/2.98  tff('#skF_4', type, '#skF_4': $i).
% 7.78/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.78/2.98  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.78/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.78/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.78/2.98  
% 7.78/3.00  tff(f_179, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 7.78/3.00  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.78/3.00  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.78/3.00  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.78/3.00  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.78/3.00  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.78/3.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.78/3.00  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.78/3.00  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.78/3.00  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.78/3.00  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.78/3.00  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.78/3.00  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 7.78/3.00  tff(f_119, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.78/3.00  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 7.78/3.00  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.78/3.00  tff(f_115, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.78/3.00  tff(f_97, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.78/3.00  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 7.78/3.00  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 7.78/3.00  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_301, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.78/3.00  tff(c_313, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_301])).
% 7.78/3.00  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_315, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_64])).
% 7.78/3.00  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/3.00  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_113, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.78/3.00  tff(c_122, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_113])).
% 7.78/3.00  tff(c_129, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_122])).
% 7.78/3.00  tff(c_435, plain, (![A_121, B_122, C_123]: (m1_subset_1(k2_relset_1(A_121, B_122, C_123), k1_zfmisc_1(B_122)) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.78/3.00  tff(c_466, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_313, c_435])).
% 7.78/3.00  tff(c_479, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_466])).
% 7.78/3.00  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.00  tff(c_502, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_479, c_8])).
% 7.78/3.00  tff(c_314, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_301])).
% 7.78/3.00  tff(c_463, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_314, c_435])).
% 7.78/3.00  tff(c_477, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_463])).
% 7.78/3.00  tff(c_487, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_477, c_8])).
% 7.78/3.00  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.78/3.00  tff(c_66, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_374, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.78/3.00  tff(c_387, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_374])).
% 7.78/3.00  tff(c_4666, plain, (![B_368, A_369, C_370]: (k1_xboole_0=B_368 | k1_relset_1(A_369, B_368, C_370)=A_369 | ~v1_funct_2(C_370, A_369, B_368) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_369, B_368))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.78/3.00  tff(c_4690, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_4666])).
% 7.78/3.00  tff(c_4703, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_387, c_4690])).
% 7.78/3.00  tff(c_4704, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_66, c_4703])).
% 7.78/3.00  tff(c_160, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.78/3.00  tff(c_173, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_160])).
% 7.78/3.00  tff(c_223, plain, (![B_96, A_97]: (k7_relat_1(B_96, A_97)=B_96 | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.78/3.00  tff(c_229, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_173, c_223])).
% 7.78/3.00  tff(c_238, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_229])).
% 7.78/3.00  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.78/3.00  tff(c_249, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_238, c_16])).
% 7.78/3.00  tff(c_253, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_249])).
% 7.78/3.00  tff(c_4993, plain, (![A_374, C_375, B_376]: (r1_tarski(A_374, k10_relat_1(C_375, B_376)) | ~r1_tarski(k9_relat_1(C_375, A_374), B_376) | ~r1_tarski(A_374, k1_relat_1(C_375)) | ~v1_funct_1(C_375) | ~v1_relat_1(C_375))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.78/3.00  tff(c_5012, plain, (![B_376]: (r1_tarski('#skF_2', k10_relat_1('#skF_5', B_376)) | ~r1_tarski(k2_relat_1('#skF_5'), B_376) | ~r1_tarski('#skF_2', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_4993])).
% 7.78/3.00  tff(c_5705, plain, (![B_407]: (r1_tarski('#skF_2', k10_relat_1('#skF_5', B_407)) | ~r1_tarski(k2_relat_1('#skF_5'), B_407))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_6, c_4704, c_5012])).
% 7.78/3.00  tff(c_5718, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_487, c_5705])).
% 7.78/3.00  tff(c_512, plain, (![A_124, B_125, C_126, D_127]: (k8_relset_1(A_124, B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/3.00  tff(c_598, plain, (![D_135]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_135)=k10_relat_1('#skF_5', D_135))), inference(resolution, [status(thm)], [c_72, c_512])).
% 7.78/3.00  tff(c_34, plain, (![A_34, B_35, C_36, D_37]: (m1_subset_1(k8_relset_1(A_34, B_35, C_36, D_37), k1_zfmisc_1(A_34)) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.78/3.00  tff(c_604, plain, (![D_135]: (m1_subset_1(k10_relat_1('#skF_5', D_135), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_598, c_34])).
% 7.78/3.00  tff(c_612, plain, (![D_136]: (m1_subset_1(k10_relat_1('#skF_5', D_136), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_604])).
% 7.78/3.00  tff(c_621, plain, (![D_137]: (r1_tarski(k10_relat_1('#skF_5', D_137), '#skF_2'))), inference(resolution, [status(thm)], [c_612, c_8])).
% 7.78/3.00  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.78/3.00  tff(c_628, plain, (![D_137]: (k10_relat_1('#skF_5', D_137)='#skF_2' | ~r1_tarski('#skF_2', k10_relat_1('#skF_5', D_137)))), inference(resolution, [status(thm)], [c_621, c_2])).
% 7.78/3.00  tff(c_5781, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_5718, c_628])).
% 7.78/3.00  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_5478, plain, (![B_397, C_402, F_399, E_398, A_400, D_401]: (k1_partfun1(A_400, B_397, C_402, D_401, E_398, F_399)=k5_relat_1(E_398, F_399) | ~m1_subset_1(F_399, k1_zfmisc_1(k2_zfmisc_1(C_402, D_401))) | ~v1_funct_1(F_399) | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(A_400, B_397))) | ~v1_funct_1(E_398))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.78/3.00  tff(c_5503, plain, (![A_400, B_397, E_398]: (k1_partfun1(A_400, B_397, '#skF_2', '#skF_3', E_398, '#skF_5')=k5_relat_1(E_398, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(A_400, B_397))) | ~v1_funct_1(E_398))), inference(resolution, [status(thm)], [c_72, c_5478])).
% 7.78/3.00  tff(c_7362, plain, (![A_460, B_461, E_462]: (k1_partfun1(A_460, B_461, '#skF_2', '#skF_3', E_462, '#skF_5')=k5_relat_1(E_462, '#skF_5') | ~m1_subset_1(E_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~v1_funct_1(E_462))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5503])).
% 7.78/3.00  tff(c_7410, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_7362])).
% 7.78/3.00  tff(c_7434, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7410])).
% 7.78/3.00  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_1474, plain, (![A_207, F_203, D_204, B_206, E_202, C_205]: (k4_relset_1(A_207, B_206, C_205, D_204, E_202, F_203)=k5_relat_1(E_202, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_205, D_204))) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.78/3.00  tff(c_2020, plain, (![A_230, B_231, E_232]: (k4_relset_1(A_230, B_231, '#skF_2', '#skF_3', E_232, '#skF_5')=k5_relat_1(E_232, '#skF_5') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(resolution, [status(thm)], [c_72, c_1474])).
% 7.78/3.00  tff(c_2066, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_2020])).
% 7.78/3.00  tff(c_32, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k4_relset_1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.78/3.00  tff(c_2389, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2066, c_32])).
% 7.78/3.00  tff(c_2393, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_2389])).
% 7.78/3.00  tff(c_2459, plain, (r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_2393, c_8])).
% 7.78/3.00  tff(c_1779, plain, (![C_225, B_220, A_223, E_221, D_224, F_222]: (k1_partfun1(A_223, B_220, C_225, D_224, E_221, F_222)=k5_relat_1(E_221, F_222) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(C_225, D_224))) | ~v1_funct_1(F_222) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_220))) | ~v1_funct_1(E_221))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.78/3.00  tff(c_1802, plain, (![A_223, B_220, E_221]: (k1_partfun1(A_223, B_220, '#skF_2', '#skF_3', E_221, '#skF_5')=k5_relat_1(E_221, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_220))) | ~v1_funct_1(E_221))), inference(resolution, [status(thm)], [c_72, c_1779])).
% 7.78/3.00  tff(c_4002, plain, (![A_309, B_310, E_311]: (k1_partfun1(A_309, B_310, '#skF_2', '#skF_3', E_311, '#skF_5')=k5_relat_1(E_311, '#skF_5') | ~m1_subset_1(E_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_1(E_311))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1802])).
% 7.78/3.00  tff(c_4050, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_4002])).
% 7.78/3.00  tff(c_4074, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4050])).
% 7.78/3.00  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.78/3.00  tff(c_469, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_435])).
% 7.78/3.00  tff(c_684, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_469])).
% 7.78/3.00  tff(c_839, plain, (~r1_tarski(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_684])).
% 7.78/3.00  tff(c_4110, plain, (~r1_tarski(k5_relat_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_839])).
% 7.78/3.00  tff(c_4115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2459, c_4110])).
% 7.78/3.00  tff(c_4117, plain, (m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_469])).
% 7.78/3.00  tff(c_38, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.78/3.00  tff(c_4282, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))=k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4117, c_38])).
% 7.78/3.00  tff(c_4300, plain, (k2_relat_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4282])).
% 7.78/3.00  tff(c_7447, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7434, c_4300])).
% 7.78/3.00  tff(c_5118, plain, (![C_380, D_379, B_381, E_377, F_378, A_382]: (k4_relset_1(A_382, B_381, C_380, D_379, E_377, F_378)=k5_relat_1(E_377, F_378) | ~m1_subset_1(F_378, k1_zfmisc_1(k2_zfmisc_1(C_380, D_379))) | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(A_382, B_381))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.78/3.00  tff(c_5721, plain, (![A_408, B_409, E_410]: (k4_relset_1(A_408, B_409, '#skF_2', '#skF_3', E_410, '#skF_5')=k5_relat_1(E_410, '#skF_5') | ~m1_subset_1(E_410, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))))), inference(resolution, [status(thm)], [c_72, c_5118])).
% 7.78/3.00  tff(c_5771, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_5721])).
% 7.78/3.00  tff(c_5894, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5771, c_32])).
% 7.78/3.00  tff(c_5898, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_5894])).
% 7.78/3.00  tff(c_5958, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_5898, c_38])).
% 7.78/3.00  tff(c_475, plain, (![A_121, B_122, C_123]: (r1_tarski(k2_relset_1(A_121, B_122, C_123), B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(resolution, [status(thm)], [c_435, c_8])).
% 7.78/3.00  tff(c_5955, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5')), '#skF_3')), inference(resolution, [status(thm)], [c_5898, c_475])).
% 7.78/3.00  tff(c_6533, plain, (r1_tarski(k2_relat_1(k5_relat_1('#skF_4', '#skF_5')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5958, c_5955])).
% 7.78/3.00  tff(c_6554, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_6533, c_2])).
% 7.78/3.00  tff(c_7124, plain, (~r1_tarski('#skF_3', k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_6554])).
% 7.78/3.00  tff(c_7461, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7447, c_7124])).
% 7.78/3.00  tff(c_7468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7461])).
% 7.78/3.00  tff(c_7469, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_6554])).
% 7.78/3.00  tff(c_119, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_113])).
% 7.78/3.00  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_119])).
% 7.78/3.00  tff(c_172, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_160])).
% 7.78/3.00  tff(c_232, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_172, c_223])).
% 7.78/3.00  tff(c_241, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_232])).
% 7.78/3.00  tff(c_258, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_241, c_16])).
% 7.78/3.00  tff(c_262, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_258])).
% 7.78/3.00  tff(c_324, plain, (![B_107, A_108]: (k9_relat_1(B_107, k2_relat_1(A_108))=k2_relat_1(k5_relat_1(A_108, B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.78/3.00  tff(c_7964, plain, (![B_472, A_473, B_474]: (k2_relat_1(k5_relat_1(k7_relat_1(B_472, A_473), B_474))=k9_relat_1(B_474, k9_relat_1(B_472, A_473)) | ~v1_relat_1(B_474) | ~v1_relat_1(k7_relat_1(B_472, A_473)) | ~v1_relat_1(B_472))), inference(superposition, [status(thm), theory('equality')], [c_16, c_324])).
% 7.78/3.00  tff(c_8018, plain, (![B_474]: (k9_relat_1(B_474, k9_relat_1('#skF_4', '#skF_1'))=k2_relat_1(k5_relat_1('#skF_4', B_474)) | ~v1_relat_1(B_474) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_7964])).
% 7.78/3.00  tff(c_8038, plain, (![B_475]: (k9_relat_1(B_475, k2_relat_1('#skF_4'))=k2_relat_1(k5_relat_1('#skF_4', B_475)) | ~v1_relat_1(B_475))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_241, c_262, c_8018])).
% 7.78/3.00  tff(c_68, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.78/3.00  tff(c_24, plain, (![B_21, A_20]: (k10_relat_1(B_21, k9_relat_1(B_21, A_20))=A_20 | ~v2_funct_1(B_21) | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.78/3.00  tff(c_4711, plain, (![A_20]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_20))=A_20 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_20, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4704, c_24])).
% 7.78/3.00  tff(c_4738, plain, (![A_20]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76, c_68, c_4711])).
% 7.78/3.00  tff(c_8048, plain, (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1('#skF_4', '#skF_5')))=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8038, c_4738])).
% 7.78/3.00  tff(c_8072, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_502, c_5781, c_7469, c_8048])).
% 7.78/3.00  tff(c_8074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_8072])).
% 7.78/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/3.00  
% 7.78/3.00  Inference rules
% 7.78/3.00  ----------------------
% 7.78/3.00  #Ref     : 0
% 7.78/3.00  #Sup     : 1851
% 7.78/3.00  #Fact    : 0
% 7.78/3.00  #Define  : 0
% 7.78/3.00  #Split   : 32
% 7.78/3.00  #Chain   : 0
% 7.78/3.00  #Close   : 0
% 7.78/3.00  
% 7.78/3.00  Ordering : KBO
% 7.78/3.00  
% 7.78/3.00  Simplification rules
% 7.78/3.00  ----------------------
% 7.78/3.00  #Subsume      : 169
% 7.78/3.00  #Demod        : 1142
% 7.78/3.00  #Tautology    : 646
% 7.78/3.00  #SimpNegUnit  : 63
% 7.78/3.00  #BackRed      : 64
% 7.78/3.00  
% 7.78/3.00  #Partial instantiations: 0
% 7.78/3.00  #Strategies tried      : 1
% 7.78/3.00  
% 7.78/3.00  Timing (in seconds)
% 7.78/3.01  ----------------------
% 7.78/3.01  Preprocessing        : 0.33
% 7.78/3.01  Parsing              : 0.17
% 7.78/3.01  CNF conversion       : 0.03
% 7.78/3.01  Main loop            : 1.78
% 7.78/3.01  Inferencing          : 0.52
% 7.78/3.01  Reduction            : 0.71
% 7.78/3.01  Demodulation         : 0.53
% 7.78/3.01  BG Simplification    : 0.06
% 7.78/3.01  Subsumption          : 0.35
% 7.78/3.01  Abstraction          : 0.07
% 7.78/3.01  MUC search           : 0.00
% 7.78/3.01  Cooper               : 0.00
% 7.78/3.01  Total                : 2.16
% 7.78/3.01  Index Insertion      : 0.00
% 7.78/3.01  Index Deletion       : 0.00
% 7.78/3.01  Index Matching       : 0.00
% 7.78/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
