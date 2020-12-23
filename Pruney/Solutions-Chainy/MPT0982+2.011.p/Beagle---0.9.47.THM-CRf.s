%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 503 expanded)
%              Number of leaves         :   45 ( 200 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 (1804 expanded)
%              Number of equality atoms :   75 ( 480 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_165,negated_conjecture,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
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

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_212,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_219,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_212])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_221,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_58])).

tff(c_88,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_95,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_88])).

tff(c_105,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_112,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_231,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_239,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_231])).

tff(c_369,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_375,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_369])).

tff(c_381,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_239,c_375])).

tff(c_382,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_381])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_88])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_113,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_105])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_650,plain,(
    ! [E_140,C_143,D_141,A_138,F_139,B_142] :
      ( k1_partfun1(A_138,B_142,C_143,D_141,E_140,F_139) = k5_relat_1(E_140,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_143,D_141)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_142)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_654,plain,(
    ! [A_138,B_142,E_140] :
      ( k1_partfun1(A_138,B_142,'#skF_2','#skF_3',E_140,'#skF_5') = k5_relat_1(E_140,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_142)))
      | ~ v1_funct_1(E_140) ) ),
    inference(resolution,[status(thm)],[c_66,c_650])).

tff(c_859,plain,(
    ! [A_163,B_164,E_165] :
      ( k1_partfun1(A_163,B_164,'#skF_2','#skF_3',E_165,'#skF_5') = k5_relat_1(E_165,'#skF_5')
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(E_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_654])).

tff(c_865,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_859])).

tff(c_872,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_865])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_895,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_64])).

tff(c_52,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_899,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_52])).

tff(c_903,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_899])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_939,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_903,c_32])).

tff(c_976,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_939])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_14,B_16)),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_130,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_130,c_18])).

tff(c_142,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_139])).

tff(c_162,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(k7_relat_1(B_74,A_75)) = k9_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_162])).

tff(c_190,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_183])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_498,plain,(
    ! [B_122,A_123,A_124] :
      ( r1_tarski(k9_relat_1(B_122,A_123),A_124)
      | ~ v5_relat_1(k7_relat_1(B_122,A_123),A_124)
      | ~ v1_relat_1(k7_relat_1(B_122,A_123))
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_10])).

tff(c_508,plain,(
    ! [A_124] :
      ( r1_tarski(k9_relat_1('#skF_5','#skF_2'),A_124)
      | ~ v5_relat_1('#skF_5',A_124)
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_498])).

tff(c_519,plain,(
    ! [A_125] :
      ( r1_tarski(k2_relat_1('#skF_5'),A_125)
      | ~ v5_relat_1('#skF_5',A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_96,c_142,c_190,c_508])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_568,plain,(
    ! [A_133] :
      ( k2_relat_1('#skF_5') = A_133
      | ~ r1_tarski(A_133,k2_relat_1('#skF_5'))
      | ~ v5_relat_1('#skF_5',A_133) ) ),
    inference(resolution,[status(thm)],[c_519,c_2])).

tff(c_580,plain,(
    ! [A_14] :
      ( k2_relat_1(k5_relat_1(A_14,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_14,'#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_568])).

tff(c_596,plain,(
    ! [A_14] :
      ( k2_relat_1(k5_relat_1(A_14,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_14,'#skF_5')))
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_580])).

tff(c_1036,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_596])).

tff(c_1064,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_113,c_976,c_1036])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,A_17)) = A_17
      | ~ v2_funct_1(B_18)
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_387,plain,(
    ! [A_17] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_17)) = A_17
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_17,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_22])).

tff(c_434,plain,(
    ! [A_120] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_120)) = A_120
      | ~ r1_tarski(A_120,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_70,c_62,c_387])).

tff(c_443,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_434])).

tff(c_447,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_443])).

tff(c_1088,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1064,c_447])).

tff(c_129,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_122])).

tff(c_133,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_18])).

tff(c_136,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_133])).

tff(c_186,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_162])).

tff(c_192,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_186])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_979,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_903,c_24])).

tff(c_28,plain,(
    ! [C_24,A_22,B_23] :
      ( v4_relat_1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_977,plain,(
    v4_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_903,c_28])).

tff(c_1029,plain,
    ( k7_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_977,c_18])).

tff(c_1032,plain,(
    k7_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1029])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1629,plain,
    ( k9_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = k2_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_12])).

tff(c_1645,plain,(
    k9_relat_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_976,c_1629])).

tff(c_14,plain,(
    ! [B_8,C_10,A_7] :
      ( k9_relat_1(k5_relat_1(B_8,C_10),A_7) = k9_relat_1(C_10,k9_relat_1(B_8,A_7))
      | ~ v1_relat_1(C_10)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1660,plain,
    ( k9_relat_1('#skF_5',k9_relat_1('#skF_4','#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_14])).

tff(c_1676,plain,(
    k9_relat_1('#skF_5',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_96,c_192,c_1660])).

tff(c_360,plain,(
    ! [B_112,A_113] :
      ( k10_relat_1(B_112,k9_relat_1(B_112,A_113)) = A_113
      | ~ v2_funct_1(B_112)
      | ~ r1_tarski(A_113,k1_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_367,plain,(
    ! [B_112,B_4] :
      ( k10_relat_1(B_112,k9_relat_1(B_112,k2_relat_1(B_4))) = k2_relat_1(B_4)
      | ~ v2_funct_1(B_112)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v5_relat_1(B_4,k1_relat_1(B_112))
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_1685,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_367])).

tff(c_1704,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_112,c_382,c_96,c_70,c_62,c_1088,c_1685])).

tff(c_1706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_1704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.83  
% 4.51/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.51/1.83  
% 4.51/1.83  %Foreground sorts:
% 4.51/1.83  
% 4.51/1.83  
% 4.51/1.83  %Background operators:
% 4.51/1.83  
% 4.51/1.83  
% 4.51/1.83  %Foreground operators:
% 4.51/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.51/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.51/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.51/1.83  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.51/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.51/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.83  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.51/1.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.51/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.83  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.51/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.51/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.51/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.83  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.51/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.51/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.83  
% 4.51/1.85  tff(f_165, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 4.51/1.85  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.85  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.85  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.51/1.85  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.85  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.85  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.51/1.85  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.51/1.85  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.51/1.85  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.51/1.85  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.51/1.85  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.51/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.85  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.51/1.85  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 4.51/1.85  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_212, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.85  tff(c_219, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_212])).
% 4.51/1.85  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_221, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_58])).
% 4.51/1.85  tff(c_88, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.51/1.85  tff(c_95, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_88])).
% 4.51/1.85  tff(c_105, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.85  tff(c_112, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_105])).
% 4.51/1.85  tff(c_60, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_231, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.51/1.85  tff(c_239, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_231])).
% 4.51/1.85  tff(c_369, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.51/1.85  tff(c_375, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_369])).
% 4.51/1.85  tff(c_381, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_239, c_375])).
% 4.51/1.85  tff(c_382, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_381])).
% 4.51/1.85  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_88])).
% 4.51/1.85  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_62, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_113, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_105])).
% 4.51/1.85  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_650, plain, (![E_140, C_143, D_141, A_138, F_139, B_142]: (k1_partfun1(A_138, B_142, C_143, D_141, E_140, F_139)=k5_relat_1(E_140, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_143, D_141))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_142))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.51/1.85  tff(c_654, plain, (![A_138, B_142, E_140]: (k1_partfun1(A_138, B_142, '#skF_2', '#skF_3', E_140, '#skF_5')=k5_relat_1(E_140, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_142))) | ~v1_funct_1(E_140))), inference(resolution, [status(thm)], [c_66, c_650])).
% 4.51/1.85  tff(c_859, plain, (![A_163, B_164, E_165]: (k1_partfun1(A_163, B_164, '#skF_2', '#skF_3', E_165, '#skF_5')=k5_relat_1(E_165, '#skF_5') | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(E_165))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_654])).
% 4.51/1.85  tff(c_865, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_859])).
% 4.51/1.85  tff(c_872, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_865])).
% 4.51/1.85  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 4.51/1.85  tff(c_895, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_872, c_64])).
% 4.51/1.85  tff(c_52, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.51/1.85  tff(c_899, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_872, c_52])).
% 4.51/1.85  tff(c_903, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_899])).
% 4.51/1.85  tff(c_32, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.85  tff(c_939, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_903, c_32])).
% 4.51/1.85  tff(c_976, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_895, c_939])).
% 4.51/1.85  tff(c_20, plain, (![A_14, B_16]: (r1_tarski(k2_relat_1(k5_relat_1(A_14, B_16)), k2_relat_1(B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.51/1.85  tff(c_122, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.85  tff(c_130, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_122])).
% 4.51/1.85  tff(c_18, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.85  tff(c_139, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_130, c_18])).
% 4.51/1.85  tff(c_142, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_139])).
% 4.51/1.85  tff(c_162, plain, (![B_74, A_75]: (k2_relat_1(k7_relat_1(B_74, A_75))=k9_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.85  tff(c_183, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_142, c_162])).
% 4.51/1.85  tff(c_190, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_183])).
% 4.51/1.85  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.51/1.85  tff(c_498, plain, (![B_122, A_123, A_124]: (r1_tarski(k9_relat_1(B_122, A_123), A_124) | ~v5_relat_1(k7_relat_1(B_122, A_123), A_124) | ~v1_relat_1(k7_relat_1(B_122, A_123)) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_162, c_10])).
% 4.51/1.85  tff(c_508, plain, (![A_124]: (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), A_124) | ~v5_relat_1('#skF_5', A_124) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_498])).
% 4.51/1.85  tff(c_519, plain, (![A_125]: (r1_tarski(k2_relat_1('#skF_5'), A_125) | ~v5_relat_1('#skF_5', A_125))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_96, c_142, c_190, c_508])).
% 4.51/1.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.85  tff(c_568, plain, (![A_133]: (k2_relat_1('#skF_5')=A_133 | ~r1_tarski(A_133, k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', A_133))), inference(resolution, [status(thm)], [c_519, c_2])).
% 4.51/1.85  tff(c_580, plain, (![A_14]: (k2_relat_1(k5_relat_1(A_14, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_14, '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_20, c_568])).
% 4.51/1.85  tff(c_596, plain, (![A_14]: (k2_relat_1(k5_relat_1(A_14, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_14, '#skF_5'))) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_580])).
% 4.51/1.85  tff(c_1036, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_976, c_596])).
% 4.51/1.85  tff(c_1064, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_113, c_976, c_1036])).
% 4.51/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.85  tff(c_22, plain, (![B_18, A_17]: (k10_relat_1(B_18, k9_relat_1(B_18, A_17))=A_17 | ~v2_funct_1(B_18) | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.85  tff(c_387, plain, (![A_17]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_17))=A_17 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_17, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_22])).
% 4.51/1.85  tff(c_434, plain, (![A_120]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_120))=A_120 | ~r1_tarski(A_120, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_70, c_62, c_387])).
% 4.51/1.85  tff(c_443, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_190, c_434])).
% 4.51/1.85  tff(c_447, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_443])).
% 4.51/1.85  tff(c_1088, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1064, c_447])).
% 4.51/1.85  tff(c_129, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_122])).
% 4.51/1.85  tff(c_133, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_129, c_18])).
% 4.51/1.85  tff(c_136, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_133])).
% 4.51/1.85  tff(c_186, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_162])).
% 4.51/1.85  tff(c_192, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_186])).
% 4.51/1.85  tff(c_24, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.51/1.85  tff(c_979, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_903, c_24])).
% 4.51/1.85  tff(c_28, plain, (![C_24, A_22, B_23]: (v4_relat_1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.85  tff(c_977, plain, (v4_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_903, c_28])).
% 4.51/1.85  tff(c_1029, plain, (k7_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k5_relat_1('#skF_4', '#skF_5') | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_977, c_18])).
% 4.51/1.85  tff(c_1032, plain, (k7_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1029])).
% 4.51/1.85  tff(c_12, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.85  tff(c_1629, plain, (k9_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')=k2_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_12])).
% 4.51/1.85  tff(c_1645, plain, (k9_relat_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_976, c_1629])).
% 4.51/1.85  tff(c_14, plain, (![B_8, C_10, A_7]: (k9_relat_1(k5_relat_1(B_8, C_10), A_7)=k9_relat_1(C_10, k9_relat_1(B_8, A_7)) | ~v1_relat_1(C_10) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.51/1.85  tff(c_1660, plain, (k9_relat_1('#skF_5', k9_relat_1('#skF_4', '#skF_1'))='#skF_3' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1645, c_14])).
% 4.51/1.85  tff(c_1676, plain, (k9_relat_1('#skF_5', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_96, c_192, c_1660])).
% 4.51/1.85  tff(c_360, plain, (![B_112, A_113]: (k10_relat_1(B_112, k9_relat_1(B_112, A_113))=A_113 | ~v2_funct_1(B_112) | ~r1_tarski(A_113, k1_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.85  tff(c_367, plain, (![B_112, B_4]: (k10_relat_1(B_112, k9_relat_1(B_112, k2_relat_1(B_4)))=k2_relat_1(B_4) | ~v2_funct_1(B_112) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v5_relat_1(B_4, k1_relat_1(B_112)) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_360])).
% 4.51/1.85  tff(c_1685, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v5_relat_1('#skF_4', k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1676, c_367])).
% 4.51/1.85  tff(c_1704, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_112, c_382, c_96, c_70, c_62, c_1088, c_1685])).
% 4.51/1.85  tff(c_1706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_1704])).
% 4.51/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.85  
% 4.51/1.85  Inference rules
% 4.51/1.85  ----------------------
% 4.51/1.85  #Ref     : 0
% 4.51/1.85  #Sup     : 363
% 4.51/1.85  #Fact    : 0
% 4.51/1.85  #Define  : 0
% 4.51/1.85  #Split   : 6
% 4.51/1.85  #Chain   : 0
% 4.51/1.85  #Close   : 0
% 4.51/1.85  
% 4.51/1.85  Ordering : KBO
% 4.51/1.85  
% 4.51/1.85  Simplification rules
% 4.51/1.85  ----------------------
% 4.51/1.85  #Subsume      : 11
% 4.51/1.85  #Demod        : 434
% 4.51/1.85  #Tautology    : 149
% 4.51/1.85  #SimpNegUnit  : 7
% 4.51/1.85  #BackRed      : 19
% 4.51/1.85  
% 4.51/1.85  #Partial instantiations: 0
% 4.51/1.85  #Strategies tried      : 1
% 4.51/1.85  
% 4.51/1.85  Timing (in seconds)
% 4.51/1.85  ----------------------
% 4.51/1.85  Preprocessing        : 0.47
% 4.51/1.85  Parsing              : 0.26
% 4.51/1.85  CNF conversion       : 0.03
% 4.51/1.85  Main loop            : 0.56
% 4.51/1.85  Inferencing          : 0.20
% 4.51/1.85  Reduction            : 0.19
% 4.51/1.85  Demodulation         : 0.14
% 4.51/1.85  BG Simplification    : 0.03
% 4.51/1.85  Subsumption          : 0.09
% 4.51/1.85  Abstraction          : 0.03
% 4.51/1.85  MUC search           : 0.00
% 4.51/1.85  Cooper               : 0.00
% 4.51/1.85  Total                : 1.09
% 4.51/1.85  Index Insertion      : 0.00
% 4.51/1.85  Index Deletion       : 0.00
% 4.51/1.85  Index Matching       : 0.00
% 4.51/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
