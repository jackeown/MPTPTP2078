%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 287 expanded)
%              Number of leaves         :   47 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 ( 886 expanded)
%              Number of equality atoms :   75 ( 260 expanded)
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

tff(f_152,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_112,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_120,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_112])).

tff(c_94,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_125,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_133,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_162,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_165,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_162])).

tff(c_171,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_165])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_14])).

tff(c_182,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_178])).

tff(c_134,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k2_relat_1(B_69),A_70)
      | ~ v5_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_391,plain,(
    ! [B_104,A_105,A_106] :
      ( r1_tarski(k9_relat_1(B_104,A_105),A_106)
      | ~ v5_relat_1(k7_relat_1(B_104,A_105),A_106)
      | ~ v1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_134])).

tff(c_400,plain,(
    ! [A_106] :
      ( r1_tarski(k9_relat_1('#skF_4','#skF_1'),A_106)
      | ~ v5_relat_1('#skF_4',A_106)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_391])).

tff(c_410,plain,(
    ! [A_106] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_106)
      | ~ v5_relat_1('#skF_4',A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_102,c_171,c_182,c_400])).

tff(c_256,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_264,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_256])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_269,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_52])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_101,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_94])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_274,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_281,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_274])).

tff(c_710,plain,(
    ! [B_122,A_123,C_124] :
      ( k1_xboole_0 = B_122
      | k1_relset_1(A_123,B_122,C_124) = A_123
      | ~ v1_funct_2(C_124,A_123,B_122)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_713,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_710])).

tff(c_719,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_281,c_713])).

tff(c_720,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_719])).

tff(c_119,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [B_78,A_79] :
      ( k3_xboole_0(k2_relat_1(B_78),A_79) = k2_relat_1(B_78)
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_134,c_8])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,k3_xboole_0(k2_relat_1(B_13),A_12)) = k10_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_333,plain,(
    ! [B_95,A_96] :
      ( k10_relat_1(B_95,k2_relat_1(B_95)) = k10_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95)
      | ~ v5_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_18])).

tff(c_345,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_333])).

tff(c_362,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k10_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_345])).

tff(c_132,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_168,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_132,c_162])).

tff(c_174,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_168])).

tff(c_187,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_14])).

tff(c_191,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_187])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_373,plain,(
    ! [B_101,A_102] :
      ( k10_relat_1(B_101,k9_relat_1(B_101,A_102)) = A_102
      | ~ v2_funct_1(B_101)
      | ~ r1_tarski(A_102,k1_relat_1(B_101))
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_381,plain,(
    ! [B_101] :
      ( k10_relat_1(B_101,k9_relat_1(B_101,k1_relat_1(B_101))) = k1_relat_1(B_101)
      | ~ v2_funct_1(B_101)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_728,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_381])).

tff(c_734,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_56,c_720,c_362,c_191,c_728])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1068,plain,(
    ! [F_153,C_151,B_148,D_150,E_152,A_149] :
      ( k1_partfun1(A_149,B_148,C_151,D_150,E_152,F_153) = k5_relat_1(E_152,F_153)
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_151,D_150)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148)))
      | ~ v1_funct_1(E_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1076,plain,(
    ! [A_149,B_148,E_152] :
      ( k1_partfun1(A_149,B_148,'#skF_2','#skF_3',E_152,'#skF_5') = k5_relat_1(E_152,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148)))
      | ~ v1_funct_1(E_152) ) ),
    inference(resolution,[status(thm)],[c_60,c_1068])).

tff(c_1462,plain,(
    ! [A_160,B_161,E_162] :
      ( k1_partfun1(A_160,B_161,'#skF_2','#skF_3',E_162,'#skF_5') = k5_relat_1(E_162,'#skF_5')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1076])).

tff(c_1483,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1462])).

tff(c_1494,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1483])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1528,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_58])).

tff(c_772,plain,(
    ! [D_127,E_130,A_126,C_129,B_128,F_125] :
      ( k4_relset_1(A_126,B_128,C_129,D_127,E_130,F_125) = k5_relat_1(E_130,F_125)
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_129,D_127)))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_126,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_829,plain,(
    ! [A_133,B_134,E_135] :
      ( k4_relset_1(A_133,B_134,'#skF_2','#skF_3',E_135,'#skF_5') = k5_relat_1(E_135,'#skF_5')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(resolution,[status(thm)],[c_60,c_772])).

tff(c_837,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_829])).

tff(c_899,plain,(
    ! [E_143,A_145,C_141,B_142,D_146,F_144] :
      ( m1_subset_1(k4_relset_1(A_145,B_142,C_141,D_146,E_143,F_144),k1_zfmisc_1(k2_zfmisc_1(A_145,D_146)))
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_141,D_146)))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_940,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_899])).

tff(c_957,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_940])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1064,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_957,c_34])).

tff(c_1685,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1064])).

tff(c_16,plain,(
    ! [B_11,A_9] :
      ( k9_relat_1(B_11,k2_relat_1(A_9)) = k2_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k9_relat_1(B_17,A_16)) = A_16
      | ~ v2_funct_1(B_17)
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_730,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_16)) = A_16
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_16,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_22])).

tff(c_797,plain,(
    ! [A_132] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_132)) = A_132
      | ~ r1_tarski(A_132,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_64,c_56,c_730])).

tff(c_815,plain,(
    ! [A_9] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5'))) = k2_relat_1(A_9)
      | ~ r1_tarski(k2_relat_1(A_9),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_797])).

tff(c_826,plain,(
    ! [A_9] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_9,'#skF_5'))) = k2_relat_1(A_9)
      | ~ r1_tarski(k2_relat_1(A_9),'#skF_2')
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_815])).

tff(c_1692,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1685,c_826])).

tff(c_1717,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_734,c_1692])).

tff(c_1718,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_1717])).

tff(c_1736,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_410,c_1718])).

tff(c_1743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:41:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.69  
% 4.26/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.69  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.26/1.69  
% 4.26/1.69  %Foreground sorts:
% 4.26/1.69  
% 4.26/1.69  
% 4.26/1.69  %Background operators:
% 4.26/1.69  
% 4.26/1.69  
% 4.26/1.69  %Foreground operators:
% 4.26/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.26/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.26/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.26/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.26/1.69  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.26/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.26/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.26/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.26/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.26/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.26/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.26/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.26/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.69  
% 4.26/1.71  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 4.26/1.71  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.26/1.71  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.71  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.26/1.71  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.26/1.71  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.26/1.71  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.26/1.71  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.26/1.71  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.26/1.71  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.26/1.71  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 4.26/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.26/1.71  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.26/1.71  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.26/1.71  tff(f_102, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.26/1.71  tff(f_88, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.26/1.71  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 4.26/1.71  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_112, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.26/1.71  tff(c_120, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_112])).
% 4.26/1.71  tff(c_94, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.26/1.71  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_94])).
% 4.26/1.71  tff(c_125, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.26/1.71  tff(c_133, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_125])).
% 4.26/1.71  tff(c_162, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.26/1.71  tff(c_165, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_162])).
% 4.26/1.71  tff(c_171, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_165])).
% 4.26/1.71  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.26/1.71  tff(c_178, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_171, c_14])).
% 4.26/1.71  tff(c_182, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_178])).
% 4.26/1.71  tff(c_134, plain, (![B_69, A_70]: (r1_tarski(k2_relat_1(B_69), A_70) | ~v5_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.71  tff(c_391, plain, (![B_104, A_105, A_106]: (r1_tarski(k9_relat_1(B_104, A_105), A_106) | ~v5_relat_1(k7_relat_1(B_104, A_105), A_106) | ~v1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_14, c_134])).
% 4.26/1.71  tff(c_400, plain, (![A_106]: (r1_tarski(k9_relat_1('#skF_4', '#skF_1'), A_106) | ~v5_relat_1('#skF_4', A_106) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_391])).
% 4.26/1.71  tff(c_410, plain, (![A_106]: (r1_tarski(k2_relat_1('#skF_4'), A_106) | ~v5_relat_1('#skF_4', A_106))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_102, c_171, c_182, c_400])).
% 4.26/1.71  tff(c_256, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.71  tff(c_264, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_256])).
% 4.26/1.71  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_269, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_52])).
% 4.26/1.71  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_101, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_94])).
% 4.26/1.71  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_56, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_274, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.26/1.71  tff(c_281, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_274])).
% 4.26/1.71  tff(c_710, plain, (![B_122, A_123, C_124]: (k1_xboole_0=B_122 | k1_relset_1(A_123, B_122, C_124)=A_123 | ~v1_funct_2(C_124, A_123, B_122) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.26/1.71  tff(c_713, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_710])).
% 4.26/1.71  tff(c_719, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_281, c_713])).
% 4.26/1.71  tff(c_720, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_719])).
% 4.26/1.71  tff(c_119, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_112])).
% 4.26/1.71  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.71  tff(c_218, plain, (![B_78, A_79]: (k3_xboole_0(k2_relat_1(B_78), A_79)=k2_relat_1(B_78) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_134, c_8])).
% 4.26/1.71  tff(c_18, plain, (![B_13, A_12]: (k10_relat_1(B_13, k3_xboole_0(k2_relat_1(B_13), A_12))=k10_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.26/1.71  tff(c_333, plain, (![B_95, A_96]: (k10_relat_1(B_95, k2_relat_1(B_95))=k10_relat_1(B_95, A_96) | ~v1_relat_1(B_95) | ~v5_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_218, c_18])).
% 4.26/1.71  tff(c_345, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_119, c_333])).
% 4.26/1.71  tff(c_362, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k10_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_345])).
% 4.26/1.71  tff(c_132, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_125])).
% 4.26/1.71  tff(c_168, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_132, c_162])).
% 4.26/1.71  tff(c_174, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_168])).
% 4.26/1.71  tff(c_187, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_174, c_14])).
% 4.26/1.71  tff(c_191, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_187])).
% 4.26/1.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.71  tff(c_373, plain, (![B_101, A_102]: (k10_relat_1(B_101, k9_relat_1(B_101, A_102))=A_102 | ~v2_funct_1(B_101) | ~r1_tarski(A_102, k1_relat_1(B_101)) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.26/1.71  tff(c_381, plain, (![B_101]: (k10_relat_1(B_101, k9_relat_1(B_101, k1_relat_1(B_101)))=k1_relat_1(B_101) | ~v2_funct_1(B_101) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_6, c_373])).
% 4.26/1.71  tff(c_728, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_720, c_381])).
% 4.26/1.71  tff(c_734, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_56, c_720, c_362, c_191, c_728])).
% 4.26/1.71  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_1068, plain, (![F_153, C_151, B_148, D_150, E_152, A_149]: (k1_partfun1(A_149, B_148, C_151, D_150, E_152, F_153)=k5_relat_1(E_152, F_153) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_151, D_150))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))) | ~v1_funct_1(E_152))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.26/1.71  tff(c_1076, plain, (![A_149, B_148, E_152]: (k1_partfun1(A_149, B_148, '#skF_2', '#skF_3', E_152, '#skF_5')=k5_relat_1(E_152, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))) | ~v1_funct_1(E_152))), inference(resolution, [status(thm)], [c_60, c_1068])).
% 4.26/1.71  tff(c_1462, plain, (![A_160, B_161, E_162]: (k1_partfun1(A_160, B_161, '#skF_2', '#skF_3', E_162, '#skF_5')=k5_relat_1(E_162, '#skF_5') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(E_162))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1076])).
% 4.26/1.71  tff(c_1483, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1462])).
% 4.26/1.71  tff(c_1494, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1483])).
% 4.26/1.71  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.26/1.71  tff(c_1528, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_58])).
% 4.26/1.71  tff(c_772, plain, (![D_127, E_130, A_126, C_129, B_128, F_125]: (k4_relset_1(A_126, B_128, C_129, D_127, E_130, F_125)=k5_relat_1(E_130, F_125) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_129, D_127))) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_126, B_128))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.26/1.71  tff(c_829, plain, (![A_133, B_134, E_135]: (k4_relset_1(A_133, B_134, '#skF_2', '#skF_3', E_135, '#skF_5')=k5_relat_1(E_135, '#skF_5') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(resolution, [status(thm)], [c_60, c_772])).
% 4.26/1.71  tff(c_837, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_829])).
% 4.26/1.71  tff(c_899, plain, (![E_143, A_145, C_141, B_142, D_146, F_144]: (m1_subset_1(k4_relset_1(A_145, B_142, C_141, D_146, E_143, F_144), k1_zfmisc_1(k2_zfmisc_1(A_145, D_146))) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_141, D_146))) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_142))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.26/1.71  tff(c_940, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_837, c_899])).
% 4.26/1.71  tff(c_957, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_940])).
% 4.26/1.71  tff(c_34, plain, (![A_33, B_34, C_35]: (k2_relset_1(A_33, B_34, C_35)=k2_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.71  tff(c_1064, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_957, c_34])).
% 4.26/1.71  tff(c_1685, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1064])).
% 4.26/1.71  tff(c_16, plain, (![B_11, A_9]: (k9_relat_1(B_11, k2_relat_1(A_9))=k2_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.26/1.71  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k9_relat_1(B_17, A_16))=A_16 | ~v2_funct_1(B_17) | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.26/1.71  tff(c_730, plain, (![A_16]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_16))=A_16 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_16, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_720, c_22])).
% 4.26/1.71  tff(c_797, plain, (![A_132]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_132))=A_132 | ~r1_tarski(A_132, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_64, c_56, c_730])).
% 4.26/1.71  tff(c_815, plain, (![A_9]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5')))=k2_relat_1(A_9) | ~r1_tarski(k2_relat_1(A_9), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_797])).
% 4.26/1.71  tff(c_826, plain, (![A_9]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_9, '#skF_5')))=k2_relat_1(A_9) | ~r1_tarski(k2_relat_1(A_9), '#skF_2') | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_815])).
% 4.26/1.71  tff(c_1692, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1685, c_826])).
% 4.26/1.71  tff(c_1717, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_734, c_1692])).
% 4.26/1.71  tff(c_1718, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_269, c_1717])).
% 4.26/1.71  tff(c_1736, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_410, c_1718])).
% 4.26/1.71  tff(c_1743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_1736])).
% 4.26/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.71  
% 4.26/1.71  Inference rules
% 4.26/1.71  ----------------------
% 4.26/1.71  #Ref     : 0
% 4.26/1.71  #Sup     : 382
% 4.26/1.71  #Fact    : 0
% 4.26/1.71  #Define  : 0
% 4.26/1.71  #Split   : 5
% 4.26/1.71  #Chain   : 0
% 4.26/1.71  #Close   : 0
% 4.26/1.71  
% 4.26/1.71  Ordering : KBO
% 4.26/1.71  
% 4.26/1.71  Simplification rules
% 4.26/1.71  ----------------------
% 4.26/1.71  #Subsume      : 6
% 4.26/1.71  #Demod        : 326
% 4.26/1.71  #Tautology    : 173
% 4.26/1.71  #SimpNegUnit  : 9
% 4.26/1.71  #BackRed      : 11
% 4.26/1.71  
% 4.26/1.71  #Partial instantiations: 0
% 4.26/1.71  #Strategies tried      : 1
% 4.26/1.71  
% 4.26/1.71  Timing (in seconds)
% 4.26/1.71  ----------------------
% 4.26/1.72  Preprocessing        : 0.36
% 4.26/1.72  Parsing              : 0.19
% 4.26/1.72  CNF conversion       : 0.02
% 4.26/1.72  Main loop            : 0.58
% 4.26/1.72  Inferencing          : 0.21
% 4.26/1.72  Reduction            : 0.19
% 4.26/1.72  Demodulation         : 0.14
% 4.26/1.72  BG Simplification    : 0.03
% 4.26/1.72  Subsumption          : 0.10
% 4.26/1.72  Abstraction          : 0.03
% 4.26/1.72  MUC search           : 0.00
% 4.26/1.72  Cooper               : 0.00
% 4.26/1.72  Total                : 0.98
% 4.26/1.72  Index Insertion      : 0.00
% 4.26/1.72  Index Deletion       : 0.00
% 4.26/1.72  Index Matching       : 0.00
% 4.26/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
