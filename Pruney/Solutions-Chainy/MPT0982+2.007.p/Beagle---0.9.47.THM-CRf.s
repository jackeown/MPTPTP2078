%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 758 expanded)
%              Number of leaves         :   46 ( 295 expanded)
%              Depth                    :   20
%              Number of atoms          :  261 (2925 expanded)
%              Number of equality atoms :   60 ( 791 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_211,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_219,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_211])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_224,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_62])).

tff(c_101,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_101])).

tff(c_138,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_146,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_138])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_22,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_229,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_236,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_229])).

tff(c_465,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_468,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_465])).

tff(c_474,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_236,c_468])).

tff(c_475,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_474])).

tff(c_18,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_316,plain,(
    ! [A_94] :
      ( k5_relat_1(A_94,k2_funct_1(A_94)) = k6_relat_1(k1_relat_1(A_94))
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_8,B_10)),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_322,plain,(
    ! [A_94] :
      ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_94))),k2_relat_1(k2_funct_1(A_94)))
      | ~ v1_relat_1(k2_funct_1(A_94))
      | ~ v1_relat_1(A_94)
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_14])).

tff(c_627,plain,(
    ! [A_146] :
      ( r1_tarski(k1_relat_1(A_146),k2_relat_1(k2_funct_1(A_146)))
      | ~ v1_relat_1(k2_funct_1(A_146))
      | ~ v1_relat_1(A_146)
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_322])).

tff(c_638,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_627])).

tff(c_647,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74,c_66,c_108,c_638])).

tff(c_661,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_664,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_661])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74,c_66,c_664])).

tff(c_670,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_32,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k2_funct_1(A_17)) = k6_relat_1(k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_145,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_587,plain,(
    ! [B_137,A_136,E_141,F_140,C_138,D_139] :
      ( k1_partfun1(A_136,B_137,C_138,D_139,E_141,F_140) = k5_relat_1(E_141,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_138,D_139)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_589,plain,(
    ! [A_136,B_137,E_141] :
      ( k1_partfun1(A_136,B_137,'#skF_2','#skF_3',E_141,'#skF_5') = k5_relat_1(E_141,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(E_141) ) ),
    inference(resolution,[status(thm)],[c_70,c_587])).

tff(c_907,plain,(
    ! [A_158,B_159,E_160] :
      ( k1_partfun1(A_158,B_159,'#skF_2','#skF_3',E_160,'#skF_5') = k5_relat_1(E_160,'#skF_5')
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(E_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_589])).

tff(c_922,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_907])).

tff(c_935,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_922])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1023,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_68])).

tff(c_56,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1027,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_56])).

tff(c_1031,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1027])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1076,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1031,c_42])).

tff(c_1112,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1076])).

tff(c_147,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v5_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [B_88,A_89] :
      ( k2_relat_1(B_88) = A_89
      | ~ r1_tarski(A_89,k2_relat_1(B_88))
      | ~ v5_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_279,plain,(
    ! [A_8,B_10] :
      ( k2_relat_1(k5_relat_1(A_8,B_10)) = k2_relat_1(B_10)
      | ~ v5_relat_1(B_10,k2_relat_1(k5_relat_1(A_8,B_10)))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_255])).

tff(c_1136,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_279])).

tff(c_1176,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_145,c_1112,c_1136])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1219,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_7)) = k9_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_12])).

tff(c_1473,plain,(
    ! [B_184] :
      ( k2_relat_1(k5_relat_1('#skF_5',B_184)) = k9_relat_1(B_184,'#skF_3')
      | ~ v1_relat_1(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1219])).

tff(c_1535,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1('#skF_5'))) = k9_relat_1(k2_funct_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1473])).

tff(c_1549,plain,(
    k9_relat_1(k2_funct_1('#skF_5'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74,c_66,c_670,c_18,c_475,c_1535])).

tff(c_285,plain,(
    ! [B_90,A_91] :
      ( k10_relat_1(k2_funct_1(B_90),A_91) = k9_relat_1(B_90,A_91)
      | ~ v2_funct_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k9_relat_1(B_14,k10_relat_1(B_14,A_13)),A_13)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1037,plain,(
    ! [B_163,A_164] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_163),k9_relat_1(B_163,A_164)),A_164)
      | ~ v1_funct_1(k2_funct_1(B_163))
      | ~ v1_relat_1(k2_funct_1(B_163))
      | ~ v2_funct_1(B_163)
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_26])).

tff(c_11513,plain,(
    ! [B_548,A_549] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_548),k2_relat_1(k5_relat_1(A_549,B_548))),k2_relat_1(A_549))
      | ~ v1_funct_1(k2_funct_1(B_548))
      | ~ v1_relat_1(k2_funct_1(B_548))
      | ~ v2_funct_1(B_548)
      | ~ v1_funct_1(B_548)
      | ~ v1_relat_1(B_548)
      | ~ v1_relat_1(B_548)
      | ~ v1_relat_1(A_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1037])).

tff(c_11554,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_5'),'#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_11513])).

tff(c_11587,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_108,c_108,c_74,c_66,c_670,c_1549,c_11554])).

tff(c_11593,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_11587])).

tff(c_11596,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_11593])).

tff(c_11600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_74,c_66,c_11596])).

tff(c_11601,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11587])).

tff(c_157,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(B_64) = A_65
      | ~ r1_tarski(A_65,k2_relat_1(B_64))
      | ~ v5_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_11682,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11601,c_157])).

tff(c_11687,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_146,c_11682])).

tff(c_11689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_11687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.74/4.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/4.38  
% 11.74/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/4.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.74/4.38  
% 11.74/4.38  %Foreground sorts:
% 11.74/4.38  
% 11.74/4.38  
% 11.74/4.38  %Background operators:
% 11.74/4.38  
% 11.74/4.38  
% 11.74/4.38  %Foreground operators:
% 11.74/4.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.74/4.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.74/4.38  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.74/4.38  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.74/4.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.74/4.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.74/4.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.74/4.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.74/4.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.74/4.38  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.74/4.38  tff('#skF_5', type, '#skF_5': $i).
% 11.74/4.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.74/4.38  tff('#skF_2', type, '#skF_2': $i).
% 11.74/4.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.74/4.38  tff('#skF_3', type, '#skF_3': $i).
% 11.74/4.38  tff('#skF_1', type, '#skF_1': $i).
% 11.74/4.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.74/4.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.74/4.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.74/4.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.74/4.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.74/4.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.74/4.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.74/4.38  tff('#skF_4', type, '#skF_4': $i).
% 11.74/4.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.74/4.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.74/4.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.74/4.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.74/4.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.74/4.38  
% 11.74/4.40  tff(f_171, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 11.74/4.40  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.74/4.40  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.74/4.40  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.74/4.40  tff(f_67, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 11.74/4.40  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.74/4.40  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.74/4.40  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.74/4.40  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 11.74/4.40  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 11.74/4.40  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.74/4.40  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.74/4.40  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.74/4.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.74/4.40  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 11.74/4.40  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 11.74/4.40  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 11.74/4.40  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_211, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.74/4.40  tff(c_219, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_211])).
% 11.74/4.40  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_224, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_62])).
% 11.74/4.40  tff(c_101, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.74/4.40  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_101])).
% 11.74/4.40  tff(c_138, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.74/4.40  tff(c_146, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_138])).
% 11.74/4.40  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_101])).
% 11.74/4.40  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_66, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_22, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.74/4.40  tff(c_24, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.74/4.40  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_229, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.74/4.40  tff(c_236, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_229])).
% 11.74/4.40  tff(c_465, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.74/4.40  tff(c_468, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_465])).
% 11.74/4.40  tff(c_474, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_236, c_468])).
% 11.74/4.40  tff(c_475, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_64, c_474])).
% 11.74/4.40  tff(c_18, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.74/4.40  tff(c_316, plain, (![A_94]: (k5_relat_1(A_94, k2_funct_1(A_94))=k6_relat_1(k1_relat_1(A_94)) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.74/4.40  tff(c_14, plain, (![A_8, B_10]: (r1_tarski(k2_relat_1(k5_relat_1(A_8, B_10)), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.74/4.40  tff(c_322, plain, (![A_94]: (r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_94))), k2_relat_1(k2_funct_1(A_94))) | ~v1_relat_1(k2_funct_1(A_94)) | ~v1_relat_1(A_94) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_316, c_14])).
% 11.74/4.40  tff(c_627, plain, (![A_146]: (r1_tarski(k1_relat_1(A_146), k2_relat_1(k2_funct_1(A_146))) | ~v1_relat_1(k2_funct_1(A_146)) | ~v1_relat_1(A_146) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_322])).
% 11.74/4.40  tff(c_638, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_475, c_627])).
% 11.74/4.40  tff(c_647, plain, (r1_tarski('#skF_2', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_74, c_66, c_108, c_638])).
% 11.74/4.40  tff(c_661, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_647])).
% 11.74/4.40  tff(c_664, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_661])).
% 11.74/4.40  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_74, c_66, c_664])).
% 11.74/4.40  tff(c_670, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_647])).
% 11.74/4.40  tff(c_32, plain, (![A_17]: (k5_relat_1(A_17, k2_funct_1(A_17))=k6_relat_1(k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.74/4.40  tff(c_145, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_138])).
% 11.74/4.40  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_587, plain, (![B_137, A_136, E_141, F_140, C_138, D_139]: (k1_partfun1(A_136, B_137, C_138, D_139, E_141, F_140)=k5_relat_1(E_141, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_138, D_139))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.74/4.40  tff(c_589, plain, (![A_136, B_137, E_141]: (k1_partfun1(A_136, B_137, '#skF_2', '#skF_3', E_141, '#skF_5')=k5_relat_1(E_141, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_1(E_141))), inference(resolution, [status(thm)], [c_70, c_587])).
% 11.74/4.40  tff(c_907, plain, (![A_158, B_159, E_160]: (k1_partfun1(A_158, B_159, '#skF_2', '#skF_3', E_160, '#skF_5')=k5_relat_1(E_160, '#skF_5') | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(E_160))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_589])).
% 11.74/4.40  tff(c_922, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_907])).
% 11.74/4.40  tff(c_935, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_922])).
% 11.74/4.40  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_171])).
% 11.74/4.40  tff(c_1023, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_935, c_68])).
% 11.74/4.40  tff(c_56, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.74/4.40  tff(c_1027, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_935, c_56])).
% 11.74/4.40  tff(c_1031, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1027])).
% 11.74/4.40  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.74/4.40  tff(c_1076, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1031, c_42])).
% 11.74/4.40  tff(c_1112, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1076])).
% 11.74/4.40  tff(c_147, plain, (![B_64, A_65]: (r1_tarski(k2_relat_1(B_64), A_65) | ~v5_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.74/4.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.74/4.40  tff(c_255, plain, (![B_88, A_89]: (k2_relat_1(B_88)=A_89 | ~r1_tarski(A_89, k2_relat_1(B_88)) | ~v5_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_147, c_2])).
% 11.74/4.40  tff(c_279, plain, (![A_8, B_10]: (k2_relat_1(k5_relat_1(A_8, B_10))=k2_relat_1(B_10) | ~v5_relat_1(B_10, k2_relat_1(k5_relat_1(A_8, B_10))) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_255])).
% 11.74/4.40  tff(c_1136, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_279])).
% 11.74/4.40  tff(c_1176, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_145, c_1112, c_1136])).
% 11.74/4.40  tff(c_12, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.74/4.40  tff(c_1219, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_5', B_7))=k9_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_12])).
% 11.74/4.40  tff(c_1473, plain, (![B_184]: (k2_relat_1(k5_relat_1('#skF_5', B_184))=k9_relat_1(B_184, '#skF_3') | ~v1_relat_1(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1219])).
% 11.74/4.40  tff(c_1535, plain, (k2_relat_1(k6_relat_1(k1_relat_1('#skF_5')))=k9_relat_1(k2_funct_1('#skF_5'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1473])).
% 11.74/4.40  tff(c_1549, plain, (k9_relat_1(k2_funct_1('#skF_5'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_74, c_66, c_670, c_18, c_475, c_1535])).
% 11.74/4.40  tff(c_285, plain, (![B_90, A_91]: (k10_relat_1(k2_funct_1(B_90), A_91)=k9_relat_1(B_90, A_91) | ~v2_funct_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.74/4.40  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k9_relat_1(B_14, k10_relat_1(B_14, A_13)), A_13) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.74/4.40  tff(c_1037, plain, (![B_163, A_164]: (r1_tarski(k9_relat_1(k2_funct_1(B_163), k9_relat_1(B_163, A_164)), A_164) | ~v1_funct_1(k2_funct_1(B_163)) | ~v1_relat_1(k2_funct_1(B_163)) | ~v2_funct_1(B_163) | ~v1_funct_1(B_163) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_285, c_26])).
% 11.74/4.40  tff(c_11513, plain, (![B_548, A_549]: (r1_tarski(k9_relat_1(k2_funct_1(B_548), k2_relat_1(k5_relat_1(A_549, B_548))), k2_relat_1(A_549)) | ~v1_funct_1(k2_funct_1(B_548)) | ~v1_relat_1(k2_funct_1(B_548)) | ~v2_funct_1(B_548) | ~v1_funct_1(B_548) | ~v1_relat_1(B_548) | ~v1_relat_1(B_548) | ~v1_relat_1(A_549))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1037])).
% 11.74/4.40  tff(c_11554, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_5'), '#skF_3'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_11513])).
% 11.74/4.40  tff(c_11587, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_108, c_108, c_74, c_66, c_670, c_1549, c_11554])).
% 11.74/4.40  tff(c_11593, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_11587])).
% 11.74/4.40  tff(c_11596, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_11593])).
% 11.74/4.40  tff(c_11600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_74, c_66, c_11596])).
% 11.74/4.40  tff(c_11601, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11587])).
% 11.74/4.40  tff(c_157, plain, (![B_64, A_65]: (k2_relat_1(B_64)=A_65 | ~r1_tarski(A_65, k2_relat_1(B_64)) | ~v5_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_147, c_2])).
% 11.74/4.40  tff(c_11682, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11601, c_157])).
% 11.74/4.40  tff(c_11687, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_146, c_11682])).
% 11.74/4.40  tff(c_11689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_11687])).
% 11.74/4.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/4.40  
% 11.74/4.40  Inference rules
% 11.74/4.40  ----------------------
% 11.74/4.40  #Ref     : 0
% 11.74/4.40  #Sup     : 2404
% 11.74/4.40  #Fact    : 0
% 11.74/4.40  #Define  : 0
% 11.74/4.40  #Split   : 22
% 11.74/4.40  #Chain   : 0
% 11.74/4.40  #Close   : 0
% 11.74/4.40  
% 11.74/4.40  Ordering : KBO
% 11.74/4.40  
% 11.74/4.40  Simplification rules
% 11.74/4.40  ----------------------
% 11.74/4.40  #Subsume      : 261
% 11.74/4.40  #Demod        : 3654
% 11.74/4.40  #Tautology    : 589
% 11.74/4.40  #SimpNegUnit  : 84
% 11.74/4.40  #BackRed      : 311
% 11.74/4.40  
% 11.74/4.40  #Partial instantiations: 0
% 11.74/4.40  #Strategies tried      : 1
% 11.74/4.40  
% 11.74/4.40  Timing (in seconds)
% 11.74/4.40  ----------------------
% 11.74/4.40  Preprocessing        : 0.36
% 11.74/4.40  Parsing              : 0.19
% 11.74/4.40  CNF conversion       : 0.02
% 11.74/4.40  Main loop            : 3.26
% 11.74/4.40  Inferencing          : 0.92
% 11.74/4.40  Reduction            : 1.45
% 11.74/4.40  Demodulation         : 1.12
% 11.74/4.40  BG Simplification    : 0.08
% 11.74/4.40  Subsumption          : 0.61
% 11.74/4.40  Abstraction          : 0.10
% 11.74/4.40  MUC search           : 0.00
% 11.74/4.40  Cooper               : 0.00
% 11.74/4.40  Total                : 3.66
% 11.74/4.40  Index Insertion      : 0.00
% 11.74/4.40  Index Deletion       : 0.00
% 11.74/4.41  Index Matching       : 0.00
% 11.74/4.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
