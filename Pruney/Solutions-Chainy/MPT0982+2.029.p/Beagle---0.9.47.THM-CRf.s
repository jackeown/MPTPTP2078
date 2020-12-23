%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 361 expanded)
%              Number of leaves         :   42 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (1285 expanded)
%              Number of equality atoms :   63 ( 369 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_150,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_88,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_101,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_108,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_101])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_170,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_163])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_172,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_50])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_94,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_100,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_94])).

tff(c_109,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_101])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_453,plain,(
    ! [A_113,D_116,B_114,F_115,E_117,C_118] :
      ( k1_partfun1(A_113,B_114,C_118,D_116,E_117,F_115) = k5_relat_1(E_117,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_118,D_116)))
      | ~ v1_funct_1(F_115)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_457,plain,(
    ! [A_113,B_114,E_117] :
      ( k1_partfun1(A_113,B_114,'#skF_2','#skF_3',E_117,'#skF_5') = k5_relat_1(E_117,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_117) ) ),
    inference(resolution,[status(thm)],[c_58,c_453])).

tff(c_477,plain,(
    ! [A_122,B_123,E_124] :
      ( k1_partfun1(A_122,B_123,'#skF_2','#skF_3',E_124,'#skF_5') = k5_relat_1(E_124,'#skF_5')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(E_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_457])).

tff(c_480,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_477])).

tff(c_486,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_480])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_491,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_56])).

tff(c_500,plain,(
    ! [E_127,B_126,F_129,C_130,A_128,D_125] :
      ( m1_subset_1(k1_partfun1(A_128,B_126,C_130,D_125,E_127,F_129),k1_zfmisc_1(k2_zfmisc_1(A_128,D_125)))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_130,D_125)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_549,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_500])).

tff(c_568,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_549])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_590,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_568,c_30])).

tff(c_625,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_590])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_14,B_16)),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_123,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ r1_tarski(A_75,k2_relat_1(B_74))
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_203,plain,(
    ! [A_14,B_16] :
      ( k2_relat_1(k5_relat_1(A_14,B_16)) = k2_relat_1(B_16)
      | ~ v5_relat_1(B_16,k2_relat_1(k5_relat_1(A_14,B_16)))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_191])).

tff(c_649,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_203])).

tff(c_690,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_100,c_109,c_625,c_649])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_146,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_146])).

tff(c_242,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_242])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154,c_248])).

tff(c_255,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_254])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_265,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_16])).

tff(c_273,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_265])).

tff(c_54,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,(
    ! [B_84,A_85] :
      ( k10_relat_1(B_84,k9_relat_1(B_84,A_85)) = A_85
      | ~ v2_funct_1(B_84)
      | ~ r1_tarski(A_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_219,plain,(
    ! [B_84] :
      ( k10_relat_1(B_84,k9_relat_1(B_84,k1_relat_1(B_84))) = k1_relat_1(B_84)
      | ~ v2_funct_1(B_84)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_211])).

tff(c_260,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_219])).

tff(c_269,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_62,c_54,c_255,c_260])).

tff(c_311,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_269])).

tff(c_711,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_311])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( k9_relat_1(B_13,k2_relat_1(A_11)) = k2_relat_1(k5_relat_1(A_11,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,A_17)) = A_17
      | ~ v2_funct_1(B_18)
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_262,plain,(
    ! [A_17] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_17)) = A_17
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_17,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_22])).

tff(c_342,plain,(
    ! [A_96] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_96)) = A_96
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_62,c_54,c_262])).

tff(c_363,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_11,'#skF_5'))) = k2_relat_1(A_11)
      | ~ r1_tarski(k2_relat_1(A_11),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_342])).

tff(c_377,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_11,'#skF_5'))) = k2_relat_1(A_11)
      | ~ r1_tarski(k2_relat_1(A_11),'#skF_2')
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_363])).

tff(c_646,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_377])).

tff(c_688,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_646])).

tff(c_1041,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_688])).

tff(c_1042,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_1041])).

tff(c_1045,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1042])).

tff(c_1049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_108,c_1045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:34:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.51  
% 3.46/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.46/1.52  
% 3.46/1.52  %Foreground sorts:
% 3.46/1.52  
% 3.46/1.52  
% 3.46/1.52  %Background operators:
% 3.46/1.52  
% 3.46/1.52  
% 3.46/1.52  %Foreground operators:
% 3.46/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.46/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.46/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.46/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.46/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.46/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.52  
% 3.46/1.54  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.46/1.54  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 3.46/1.54  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.46/1.54  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.46/1.54  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.46/1.54  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.46/1.54  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.46/1.54  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.46/1.54  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.46/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.54  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.46/1.54  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.46/1.54  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.46/1.54  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 3.46/1.54  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.46/1.54  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.46/1.54  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_88, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.46/1.54  tff(c_91, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_88])).
% 3.46/1.54  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_91])).
% 3.46/1.54  tff(c_101, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.46/1.54  tff(c_108, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_101])).
% 3.46/1.54  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.46/1.54  tff(c_163, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.46/1.54  tff(c_170, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_163])).
% 3.46/1.54  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_172, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_50])).
% 3.46/1.54  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_94, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.46/1.54  tff(c_100, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_94])).
% 3.46/1.54  tff(c_109, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_101])).
% 3.46/1.54  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_453, plain, (![A_113, D_116, B_114, F_115, E_117, C_118]: (k1_partfun1(A_113, B_114, C_118, D_116, E_117, F_115)=k5_relat_1(E_117, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_118, D_116))) | ~v1_funct_1(F_115) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.46/1.54  tff(c_457, plain, (![A_113, B_114, E_117]: (k1_partfun1(A_113, B_114, '#skF_2', '#skF_3', E_117, '#skF_5')=k5_relat_1(E_117, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_117))), inference(resolution, [status(thm)], [c_58, c_453])).
% 3.46/1.54  tff(c_477, plain, (![A_122, B_123, E_124]: (k1_partfun1(A_122, B_123, '#skF_2', '#skF_3', E_124, '#skF_5')=k5_relat_1(E_124, '#skF_5') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(E_124))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_457])).
% 3.46/1.54  tff(c_480, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_477])).
% 3.46/1.54  tff(c_486, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_480])).
% 3.46/1.54  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_491, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_56])).
% 3.46/1.54  tff(c_500, plain, (![E_127, B_126, F_129, C_130, A_128, D_125]: (m1_subset_1(k1_partfun1(A_128, B_126, C_130, D_125, E_127, F_129), k1_zfmisc_1(k2_zfmisc_1(A_128, D_125))) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_130, D_125))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_126))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.46/1.54  tff(c_549, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_486, c_500])).
% 3.46/1.54  tff(c_568, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_549])).
% 3.46/1.54  tff(c_30, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.46/1.54  tff(c_590, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_568, c_30])).
% 3.46/1.54  tff(c_625, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_590])).
% 3.46/1.54  tff(c_20, plain, (![A_14, B_16]: (r1_tarski(k2_relat_1(k5_relat_1(A_14, B_16)), k2_relat_1(B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.54  tff(c_123, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.46/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.54  tff(c_191, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~r1_tarski(A_75, k2_relat_1(B_74)) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.46/1.54  tff(c_203, plain, (![A_14, B_16]: (k2_relat_1(k5_relat_1(A_14, B_16))=k2_relat_1(B_16) | ~v5_relat_1(B_16, k2_relat_1(k5_relat_1(A_14, B_16))) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_20, c_191])).
% 3.46/1.54  tff(c_649, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_625, c_203])).
% 3.46/1.54  tff(c_690, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_100, c_109, c_625, c_649])).
% 3.46/1.54  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_146, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.54  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_146])).
% 3.46/1.54  tff(c_242, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.54  tff(c_248, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_242])).
% 3.46/1.54  tff(c_254, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154, c_248])).
% 3.46/1.54  tff(c_255, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_254])).
% 3.46/1.54  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.54  tff(c_265, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_16])).
% 3.46/1.54  tff(c_273, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_265])).
% 3.46/1.54  tff(c_54, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.46/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.54  tff(c_211, plain, (![B_84, A_85]: (k10_relat_1(B_84, k9_relat_1(B_84, A_85))=A_85 | ~v2_funct_1(B_84) | ~r1_tarski(A_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.54  tff(c_219, plain, (![B_84]: (k10_relat_1(B_84, k9_relat_1(B_84, k1_relat_1(B_84)))=k1_relat_1(B_84) | ~v2_funct_1(B_84) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(resolution, [status(thm)], [c_6, c_211])).
% 3.46/1.54  tff(c_260, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_219])).
% 3.46/1.54  tff(c_269, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_62, c_54, c_255, c_260])).
% 3.46/1.54  tff(c_311, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_269])).
% 3.46/1.54  tff(c_711, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_690, c_311])).
% 3.46/1.54  tff(c_18, plain, (![B_13, A_11]: (k9_relat_1(B_13, k2_relat_1(A_11))=k2_relat_1(k5_relat_1(A_11, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.46/1.54  tff(c_22, plain, (![B_18, A_17]: (k10_relat_1(B_18, k9_relat_1(B_18, A_17))=A_17 | ~v2_funct_1(B_18) | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.54  tff(c_262, plain, (![A_17]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_17))=A_17 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_17, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_22])).
% 3.46/1.54  tff(c_342, plain, (![A_96]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_96))=A_96 | ~r1_tarski(A_96, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_62, c_54, c_262])).
% 3.46/1.54  tff(c_363, plain, (![A_11]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_11, '#skF_5')))=k2_relat_1(A_11) | ~r1_tarski(k2_relat_1(A_11), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_342])).
% 3.46/1.54  tff(c_377, plain, (![A_11]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_11, '#skF_5')))=k2_relat_1(A_11) | ~r1_tarski(k2_relat_1(A_11), '#skF_2') | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_363])).
% 3.46/1.54  tff(c_646, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_625, c_377])).
% 3.46/1.54  tff(c_688, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_646])).
% 3.46/1.54  tff(c_1041, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_711, c_688])).
% 3.46/1.54  tff(c_1042, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_172, c_1041])).
% 3.46/1.54  tff(c_1045, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1042])).
% 3.46/1.54  tff(c_1049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_108, c_1045])).
% 3.46/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  Inference rules
% 3.46/1.54  ----------------------
% 3.46/1.54  #Ref     : 0
% 3.46/1.54  #Sup     : 210
% 3.46/1.54  #Fact    : 0
% 3.46/1.54  #Define  : 0
% 3.46/1.54  #Split   : 4
% 3.46/1.54  #Chain   : 0
% 3.46/1.54  #Close   : 0
% 3.46/1.54  
% 3.46/1.54  Ordering : KBO
% 3.46/1.54  
% 3.46/1.54  Simplification rules
% 3.46/1.54  ----------------------
% 3.46/1.54  #Subsume      : 6
% 3.46/1.54  #Demod        : 210
% 3.46/1.54  #Tautology    : 85
% 3.46/1.54  #SimpNegUnit  : 5
% 3.46/1.54  #BackRed      : 9
% 3.46/1.54  
% 3.46/1.54  #Partial instantiations: 0
% 3.46/1.54  #Strategies tried      : 1
% 3.46/1.54  
% 3.46/1.54  Timing (in seconds)
% 3.46/1.54  ----------------------
% 3.46/1.54  Preprocessing        : 0.36
% 3.46/1.54  Parsing              : 0.19
% 3.46/1.54  CNF conversion       : 0.02
% 3.46/1.54  Main loop            : 0.42
% 3.46/1.54  Inferencing          : 0.15
% 3.46/1.54  Reduction            : 0.14
% 3.46/1.54  Demodulation         : 0.10
% 3.46/1.54  BG Simplification    : 0.02
% 3.46/1.54  Subsumption          : 0.07
% 3.46/1.54  Abstraction          : 0.02
% 3.46/1.54  MUC search           : 0.00
% 3.46/1.54  Cooper               : 0.00
% 3.46/1.54  Total                : 0.82
% 3.46/1.54  Index Insertion      : 0.00
% 3.46/1.54  Index Deletion       : 0.00
% 3.46/1.54  Index Matching       : 0.00
% 3.46/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
