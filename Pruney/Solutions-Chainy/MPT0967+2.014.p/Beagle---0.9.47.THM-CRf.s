%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 628 expanded)
%              Number of leaves         :   30 ( 213 expanded)
%              Depth                    :   16
%              Number of atoms          :  306 (1886 expanded)
%              Number of equality atoms :   79 ( 470 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_82,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [B_48,A_49] :
      ( v5_relat_1(B_48,A_49)
      | ~ r1_tarski(k2_relat_1(B_48),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_162,plain,(
    ! [B_48] :
      ( v5_relat_1(B_48,k2_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_148,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_988,plain,(
    ! [A_119,A_120,B_121] :
      ( r1_tarski(A_119,A_120)
      | ~ r1_tarski(A_119,k2_relat_1(B_121))
      | ~ v5_relat_1(B_121,A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_1100,plain,(
    ! [B_142,A_143,B_144] :
      ( r1_tarski(k2_relat_1(B_142),A_143)
      | ~ v5_relat_1(B_144,A_143)
      | ~ v1_relat_1(B_144)
      | ~ v5_relat_1(B_142,k2_relat_1(B_144))
      | ~ v1_relat_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_14,c_988])).

tff(c_1106,plain,(
    ! [B_142] :
      ( r1_tarski(k2_relat_1(B_142),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_142,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_152,c_1100])).

tff(c_1114,plain,(
    ! [B_145] :
      ( r1_tarski(k2_relat_1(B_145),'#skF_2')
      | ~ v5_relat_1(B_145,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1106])).

tff(c_1118,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_1114])).

tff(c_1121,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1118])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_114,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,'#skF_3')
      | ~ r1_tarski(A_39,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_1139,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1121,c_114])).

tff(c_1122,plain,(
    ! [D_146,C_147,B_148,A_149] :
      ( m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(C_147,B_148)))
      | ~ r1_tarski(k2_relat_1(D_146),B_148)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(C_147,A_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1177,plain,(
    ! [B_151] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_151)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_151) ) ),
    inference(resolution,[status(thm)],[c_44,c_1122])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_209,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_213,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_714,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_720,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_714])).

tff(c_724,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_213,c_720])).

tff(c_725,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_724])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_165,plain,(
    ! [B_51] :
      ( r1_tarski(k2_relat_1(B_51),'#skF_3')
      | ~ v5_relat_1(B_51,'#skF_2')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_176,plain,(
    ! [B_52] :
      ( v5_relat_1(B_52,'#skF_3')
      | ~ v5_relat_1(B_52,'#skF_2')
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_165,c_12])).

tff(c_179,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_176])).

tff(c_182,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_179])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_164,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_420,plain,(
    ! [B_89,A_90,C_91] :
      ( k1_xboole_0 = B_89
      | k1_relset_1(A_90,B_89,C_91) = A_90
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_426,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_420])).

tff(c_430,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_213,c_426])).

tff(c_431,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_430])).

tff(c_128,plain,(
    ! [B_8] :
      ( r1_tarski(k2_relat_1(B_8),'#skF_3')
      | ~ v5_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_115])).

tff(c_326,plain,(
    ! [D_82,C_83,B_84,A_85] :
      ( m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(C_83,B_84)))
      | ~ r1_tarski(k2_relat_1(D_82),B_84)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(C_83,A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_330,plain,(
    ! [B_86] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_86)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_86) ) ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_384,plain,(
    ! [B_88] :
      ( k1_relset_1('#skF_1',B_88,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_88) ) ),
    inference(resolution,[status(thm)],[c_330,c_22])).

tff(c_392,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_384])).

tff(c_406,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_152,c_392])).

tff(c_433,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_406])).

tff(c_329,plain,(
    ! [B_84] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_84)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_84) ) ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_517,plain,(
    ! [B_94,C_95,A_96] :
      ( k1_xboole_0 = B_94
      | v1_funct_2(C_95,A_96,B_94)
      | k1_relset_1(A_96,B_94,C_95) != A_96
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_529,plain,(
    ! [B_97] :
      ( k1_xboole_0 = B_97
      | v1_funct_2('#skF_4','#skF_1',B_97)
      | k1_relset_1('#skF_1',B_97,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_97) ) ),
    inference(resolution,[status(thm)],[c_329,c_517])).

tff(c_537,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_529])).

tff(c_551,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_152,c_433,c_537])).

tff(c_552,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_551])).

tff(c_133,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(A_43,A_44)
      | ~ r1_tarski(A_43,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_143,plain,(
    ! [B_8,A_44] :
      ( r1_tarski(k2_relat_1(B_8),A_44)
      | ~ v5_relat_1(B_8,k1_xboole_0)
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_18,plain,(
    ! [C_14,B_13,A_12] :
      ( v5_relat_1(C_14,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_357,plain,(
    ! [B_87] :
      ( v5_relat_1('#skF_4',B_87)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_87) ) ),
    inference(resolution,[status(thm)],[c_330,c_18])).

tff(c_361,plain,(
    ! [A_44] :
      ( v5_relat_1('#skF_4',A_44)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_143,c_357])).

tff(c_376,plain,(
    ! [A_44] :
      ( v5_relat_1('#skF_4',A_44)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_361])).

tff(c_411,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_563,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_411])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_563])).

tff(c_687,plain,(
    ! [A_99] : v5_relat_1('#skF_4',A_99) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_92,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v5_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_99,plain,(
    ! [B_36] :
      ( k2_relat_1(B_36) = k1_xboole_0
      | ~ v5_relat_1(B_36,k1_xboole_0)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_92,c_66])).

tff(c_701,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_687,c_99])).

tff(c_713,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_701])).

tff(c_733,plain,(
    ! [B_84] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_84)))
      | ~ r1_tarski(k1_xboole_0,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_329])).

tff(c_804,plain,(
    ! [B_103] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_103))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_733])).

tff(c_816,plain,(
    ! [B_103] : k1_relset_1('#skF_1',B_103,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_804,c_22])).

tff(c_832,plain,(
    ! [B_103] : k1_relset_1('#skF_1',B_103,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_816])).

tff(c_735,plain,(
    ! [B_84] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_84))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_733])).

tff(c_849,plain,(
    ! [B_105,C_106,A_107] :
      ( k1_xboole_0 = B_105
      | v1_funct_2(C_106,A_107,B_105)
      | k1_relset_1(A_107,B_105,C_106) != A_107
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_852,plain,(
    ! [B_84] :
      ( k1_xboole_0 = B_84
      | v1_funct_2('#skF_4','#skF_1',B_84)
      | k1_relset_1('#skF_1',B_84,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_735,c_849])).

tff(c_856,plain,(
    ! [B_108] :
      ( k1_xboole_0 = B_108
      | v1_funct_2('#skF_4','#skF_1',B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_852])).

tff(c_860,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_856,c_164])).

tff(c_878,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_10])).

tff(c_67,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_68])).

tff(c_932,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1189,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1177,c_932])).

tff(c_1205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_1189])).

tff(c_1206,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1210,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_46])).

tff(c_1208,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1206,c_44])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_1208,c_50])).

tff(c_1247,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1249,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_10])).

tff(c_1248,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1254,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1248])).

tff(c_1263,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_44])).

tff(c_1287,plain,(
    ! [C_162,A_163,B_164] :
      ( v1_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1291,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1263,c_1287])).

tff(c_1656,plain,(
    ! [C_224,B_225,A_226] :
      ( v5_relat_1(C_224,B_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1660,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1263,c_1656])).

tff(c_1637,plain,(
    ! [B_218,A_219] :
      ( r1_tarski(k2_relat_1(B_218),A_219)
      | ~ v5_relat_1(B_218,A_219)
      | ~ v1_relat_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1264,plain,(
    ! [B_159,A_160] :
      ( B_159 = A_160
      | ~ r1_tarski(B_159,A_160)
      | ~ r1_tarski(A_160,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1269,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1249,c_1264])).

tff(c_1648,plain,(
    ! [B_218] :
      ( k2_relat_1(B_218) = '#skF_1'
      | ~ v5_relat_1(B_218,'#skF_1')
      | ~ v1_relat_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_1637,c_1269])).

tff(c_1663,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1660,c_1648])).

tff(c_1666,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_1663])).

tff(c_1929,plain,(
    ! [D_264,C_265,B_266,A_267] :
      ( m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(C_265,B_266)))
      | ~ r1_tarski(k2_relat_1(D_264),B_266)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(C_265,A_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1931,plain,(
    ! [B_266] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_266)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_266) ) ),
    inference(resolution,[status(thm)],[c_1263,c_1929])).

tff(c_1934,plain,(
    ! [B_266] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_266))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1666,c_1931])).

tff(c_1255,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_46])).

tff(c_1417,plain,(
    ! [A_188,B_189,C_190] :
      ( k1_relset_1(A_188,B_189,C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1421,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1263,c_1417])).

tff(c_34,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1541,plain,(
    ! [B_205,C_206] :
      ( k1_relset_1('#skF_1',B_205,C_206) = '#skF_1'
      | ~ v1_funct_2(C_206,'#skF_1',B_205)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_205))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1247,c_1247,c_1247,c_34])).

tff(c_1544,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1263,c_1541])).

tff(c_1547,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1421,c_1544])).

tff(c_1344,plain,(
    ! [C_179,B_180,A_181] :
      ( v5_relat_1(C_179,B_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1348,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1263,c_1344])).

tff(c_1293,plain,(
    ! [B_165,A_166] :
      ( r1_tarski(k2_relat_1(B_165),A_166)
      | ~ v5_relat_1(B_165,A_166)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1300,plain,(
    ! [B_165] :
      ( k2_relat_1(B_165) = '#skF_1'
      | ~ v5_relat_1(B_165,'#skF_1')
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_1293,c_1269])).

tff(c_1351,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1348,c_1300])).

tff(c_1354,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1291,c_1351])).

tff(c_1565,plain,(
    ! [D_209,C_210,B_211,A_212] :
      ( m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(C_210,B_211)))
      | ~ r1_tarski(k2_relat_1(D_209),B_211)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(C_210,A_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1567,plain,(
    ! [B_211] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_211)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_211) ) ),
    inference(resolution,[status(thm)],[c_1263,c_1565])).

tff(c_1572,plain,(
    ! [B_213] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_213))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1354,c_1567])).

tff(c_1587,plain,(
    ! [B_213] : k1_relset_1('#skF_1',B_213,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1572,c_22])).

tff(c_1607,plain,(
    ! [B_213] : k1_relset_1('#skF_1',B_213,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1587])).

tff(c_30,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1557,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,'#skF_1',B_23)
      | k1_relset_1('#skF_1',B_23,C_24) != '#skF_1'
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_23))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1247,c_1247,c_1247,c_30])).

tff(c_1600,plain,(
    ! [B_213] :
      ( v1_funct_2('#skF_4','#skF_1',B_213)
      | k1_relset_1('#skF_1',B_213,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1572,c_1557])).

tff(c_1623,plain,(
    ! [B_213] : v1_funct_2('#skF_4','#skF_1',B_213) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1607,c_1600])).

tff(c_1292,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_1627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1292])).

tff(c_1628,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1934,c_1628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.55/1.61  
% 3.55/1.61  %Foreground sorts:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Background operators:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Foreground operators:
% 3.55/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.55/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.55/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.55/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.55/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.61  
% 3.81/1.63  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 3.81/1.63  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.81/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.81/1.63  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.81/1.63  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.81/1.63  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.81/1.63  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 3.81/1.63  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.81/1.63  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.81/1.63  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.81/1.63  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_82, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.81/1.63  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_82])).
% 3.81/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.63  tff(c_153, plain, (![B_48, A_49]: (v5_relat_1(B_48, A_49) | ~r1_tarski(k2_relat_1(B_48), A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_162, plain, (![B_48]: (v5_relat_1(B_48, k2_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_6, c_153])).
% 3.81/1.63  tff(c_148, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.63  tff(c_152, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_148])).
% 3.81/1.63  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_102, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.63  tff(c_988, plain, (![A_119, A_120, B_121]: (r1_tarski(A_119, A_120) | ~r1_tarski(A_119, k2_relat_1(B_121)) | ~v5_relat_1(B_121, A_120) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_14, c_102])).
% 3.81/1.63  tff(c_1100, plain, (![B_142, A_143, B_144]: (r1_tarski(k2_relat_1(B_142), A_143) | ~v5_relat_1(B_144, A_143) | ~v1_relat_1(B_144) | ~v5_relat_1(B_142, k2_relat_1(B_144)) | ~v1_relat_1(B_142))), inference(resolution, [status(thm)], [c_14, c_988])).
% 3.81/1.63  tff(c_1106, plain, (![B_142]: (r1_tarski(k2_relat_1(B_142), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_142, k2_relat_1('#skF_4')) | ~v1_relat_1(B_142))), inference(resolution, [status(thm)], [c_152, c_1100])).
% 3.81/1.63  tff(c_1114, plain, (![B_145]: (r1_tarski(k2_relat_1(B_145), '#skF_2') | ~v5_relat_1(B_145, k2_relat_1('#skF_4')) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1106])).
% 3.81/1.63  tff(c_1118, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_162, c_1114])).
% 3.81/1.63  tff(c_1121, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1118])).
% 3.81/1.63  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_114, plain, (![A_39]: (r1_tarski(A_39, '#skF_3') | ~r1_tarski(A_39, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_102])).
% 3.81/1.63  tff(c_1139, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1121, c_114])).
% 3.81/1.63  tff(c_1122, plain, (![D_146, C_147, B_148, A_149]: (m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(C_147, B_148))) | ~r1_tarski(k2_relat_1(D_146), B_148) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(C_147, A_149))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.63  tff(c_1177, plain, (![B_151]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_151))) | ~r1_tarski(k2_relat_1('#skF_4'), B_151))), inference(resolution, [status(thm)], [c_44, c_1122])).
% 3.81/1.63  tff(c_40, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.81/1.63  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_209, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.81/1.63  tff(c_213, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_209])).
% 3.81/1.63  tff(c_714, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_720, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_714])).
% 3.81/1.63  tff(c_724, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_213, c_720])).
% 3.81/1.63  tff(c_725, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_724])).
% 3.81/1.63  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.63  tff(c_115, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_102])).
% 3.81/1.63  tff(c_165, plain, (![B_51]: (r1_tarski(k2_relat_1(B_51), '#skF_3') | ~v5_relat_1(B_51, '#skF_2') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_14, c_115])).
% 3.81/1.63  tff(c_12, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_176, plain, (![B_52]: (v5_relat_1(B_52, '#skF_3') | ~v5_relat_1(B_52, '#skF_2') | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_165, c_12])).
% 3.81/1.63  tff(c_179, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_152, c_176])).
% 3.81/1.63  tff(c_182, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_179])).
% 3.81/1.63  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_38, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.81/1.63  tff(c_50, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 3.81/1.63  tff(c_164, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.81/1.63  tff(c_420, plain, (![B_89, A_90, C_91]: (k1_xboole_0=B_89 | k1_relset_1(A_90, B_89, C_91)=A_90 | ~v1_funct_2(C_91, A_90, B_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_426, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_420])).
% 3.81/1.63  tff(c_430, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_213, c_426])).
% 3.81/1.63  tff(c_431, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_430])).
% 3.81/1.63  tff(c_128, plain, (![B_8]: (r1_tarski(k2_relat_1(B_8), '#skF_3') | ~v5_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_14, c_115])).
% 3.81/1.63  tff(c_326, plain, (![D_82, C_83, B_84, A_85]: (m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(C_83, B_84))) | ~r1_tarski(k2_relat_1(D_82), B_84) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(C_83, A_85))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.63  tff(c_330, plain, (![B_86]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_86))) | ~r1_tarski(k2_relat_1('#skF_4'), B_86))), inference(resolution, [status(thm)], [c_44, c_326])).
% 3.81/1.63  tff(c_22, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.81/1.63  tff(c_384, plain, (![B_88]: (k1_relset_1('#skF_1', B_88, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_88))), inference(resolution, [status(thm)], [c_330, c_22])).
% 3.81/1.63  tff(c_392, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_384])).
% 3.81/1.63  tff(c_406, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_152, c_392])).
% 3.81/1.63  tff(c_433, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_431, c_406])).
% 3.81/1.63  tff(c_329, plain, (![B_84]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_84))) | ~r1_tarski(k2_relat_1('#skF_4'), B_84))), inference(resolution, [status(thm)], [c_44, c_326])).
% 3.81/1.63  tff(c_517, plain, (![B_94, C_95, A_96]: (k1_xboole_0=B_94 | v1_funct_2(C_95, A_96, B_94) | k1_relset_1(A_96, B_94, C_95)!=A_96 | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_94))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_529, plain, (![B_97]: (k1_xboole_0=B_97 | v1_funct_2('#skF_4', '#skF_1', B_97) | k1_relset_1('#skF_1', B_97, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_97))), inference(resolution, [status(thm)], [c_329, c_517])).
% 3.81/1.63  tff(c_537, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_529])).
% 3.81/1.63  tff(c_551, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_152, c_433, c_537])).
% 3.81/1.63  tff(c_552, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_164, c_551])).
% 3.81/1.63  tff(c_133, plain, (![A_43, A_44]: (r1_tarski(A_43, A_44) | ~r1_tarski(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_102])).
% 3.81/1.63  tff(c_143, plain, (![B_8, A_44]: (r1_tarski(k2_relat_1(B_8), A_44) | ~v5_relat_1(B_8, k1_xboole_0) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_14, c_133])).
% 3.81/1.63  tff(c_18, plain, (![C_14, B_13, A_12]: (v5_relat_1(C_14, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.63  tff(c_357, plain, (![B_87]: (v5_relat_1('#skF_4', B_87) | ~r1_tarski(k2_relat_1('#skF_4'), B_87))), inference(resolution, [status(thm)], [c_330, c_18])).
% 3.81/1.63  tff(c_361, plain, (![A_44]: (v5_relat_1('#skF_4', A_44) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_143, c_357])).
% 3.81/1.63  tff(c_376, plain, (![A_44]: (v5_relat_1('#skF_4', A_44) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_361])).
% 3.81/1.63  tff(c_411, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_376])).
% 3.81/1.63  tff(c_563, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_411])).
% 3.81/1.63  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_563])).
% 3.81/1.63  tff(c_687, plain, (![A_99]: (v5_relat_1('#skF_4', A_99))), inference(splitRight, [status(thm)], [c_376])).
% 3.81/1.63  tff(c_92, plain, (![B_36, A_37]: (r1_tarski(k2_relat_1(B_36), A_37) | ~v5_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_55, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.63  tff(c_66, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_55])).
% 3.81/1.63  tff(c_99, plain, (![B_36]: (k2_relat_1(B_36)=k1_xboole_0 | ~v5_relat_1(B_36, k1_xboole_0) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_92, c_66])).
% 3.81/1.63  tff(c_701, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_687, c_99])).
% 3.81/1.63  tff(c_713, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_701])).
% 3.81/1.63  tff(c_733, plain, (![B_84]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_84))) | ~r1_tarski(k1_xboole_0, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_713, c_329])).
% 3.81/1.63  tff(c_804, plain, (![B_103]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_103))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_733])).
% 3.81/1.63  tff(c_816, plain, (![B_103]: (k1_relset_1('#skF_1', B_103, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_804, c_22])).
% 3.81/1.63  tff(c_832, plain, (![B_103]: (k1_relset_1('#skF_1', B_103, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_725, c_816])).
% 3.81/1.63  tff(c_735, plain, (![B_84]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_84))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_733])).
% 3.81/1.63  tff(c_849, plain, (![B_105, C_106, A_107]: (k1_xboole_0=B_105 | v1_funct_2(C_106, A_107, B_105) | k1_relset_1(A_107, B_105, C_106)!=A_107 | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_852, plain, (![B_84]: (k1_xboole_0=B_84 | v1_funct_2('#skF_4', '#skF_1', B_84) | k1_relset_1('#skF_1', B_84, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_735, c_849])).
% 3.81/1.63  tff(c_856, plain, (![B_108]: (k1_xboole_0=B_108 | v1_funct_2('#skF_4', '#skF_1', B_108))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_852])).
% 3.81/1.63  tff(c_860, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_856, c_164])).
% 3.81/1.63  tff(c_878, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_860, c_10])).
% 3.81/1.63  tff(c_67, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_55])).
% 3.81/1.63  tff(c_68, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 3.81/1.63  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_68])).
% 3.81/1.63  tff(c_932, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 3.81/1.63  tff(c_1189, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1177, c_932])).
% 3.81/1.63  tff(c_1205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1139, c_1189])).
% 3.81/1.63  tff(c_1206, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_67])).
% 3.81/1.63  tff(c_1210, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_46])).
% 3.81/1.63  tff(c_1208, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1206, c_44])).
% 3.81/1.63  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1210, c_1208, c_50])).
% 3.81/1.63  tff(c_1247, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 3.81/1.63  tff(c_1249, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_10])).
% 3.81/1.63  tff(c_1248, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.81/1.63  tff(c_1254, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1248])).
% 3.81/1.63  tff(c_1263, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_44])).
% 3.81/1.63  tff(c_1287, plain, (![C_162, A_163, B_164]: (v1_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.81/1.63  tff(c_1291, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1263, c_1287])).
% 3.81/1.63  tff(c_1656, plain, (![C_224, B_225, A_226]: (v5_relat_1(C_224, B_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.63  tff(c_1660, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1263, c_1656])).
% 3.81/1.63  tff(c_1637, plain, (![B_218, A_219]: (r1_tarski(k2_relat_1(B_218), A_219) | ~v5_relat_1(B_218, A_219) | ~v1_relat_1(B_218))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_1264, plain, (![B_159, A_160]: (B_159=A_160 | ~r1_tarski(B_159, A_160) | ~r1_tarski(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.63  tff(c_1269, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_1249, c_1264])).
% 3.81/1.63  tff(c_1648, plain, (![B_218]: (k2_relat_1(B_218)='#skF_1' | ~v5_relat_1(B_218, '#skF_1') | ~v1_relat_1(B_218))), inference(resolution, [status(thm)], [c_1637, c_1269])).
% 3.81/1.63  tff(c_1663, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1660, c_1648])).
% 3.81/1.63  tff(c_1666, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_1663])).
% 3.81/1.63  tff(c_1929, plain, (![D_264, C_265, B_266, A_267]: (m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(C_265, B_266))) | ~r1_tarski(k2_relat_1(D_264), B_266) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(C_265, A_267))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.63  tff(c_1931, plain, (![B_266]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_266))) | ~r1_tarski(k2_relat_1('#skF_4'), B_266))), inference(resolution, [status(thm)], [c_1263, c_1929])).
% 3.81/1.63  tff(c_1934, plain, (![B_266]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_266))))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1666, c_1931])).
% 3.81/1.63  tff(c_1255, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_46])).
% 3.81/1.63  tff(c_1417, plain, (![A_188, B_189, C_190]: (k1_relset_1(A_188, B_189, C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.81/1.63  tff(c_1421, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1263, c_1417])).
% 3.81/1.63  tff(c_34, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_1541, plain, (![B_205, C_206]: (k1_relset_1('#skF_1', B_205, C_206)='#skF_1' | ~v1_funct_2(C_206, '#skF_1', B_205) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_205))))), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1247, c_1247, c_1247, c_34])).
% 3.81/1.63  tff(c_1544, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1263, c_1541])).
% 3.81/1.63  tff(c_1547, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1421, c_1544])).
% 3.81/1.63  tff(c_1344, plain, (![C_179, B_180, A_181]: (v5_relat_1(C_179, B_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.63  tff(c_1348, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1263, c_1344])).
% 3.81/1.63  tff(c_1293, plain, (![B_165, A_166]: (r1_tarski(k2_relat_1(B_165), A_166) | ~v5_relat_1(B_165, A_166) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.63  tff(c_1300, plain, (![B_165]: (k2_relat_1(B_165)='#skF_1' | ~v5_relat_1(B_165, '#skF_1') | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_1293, c_1269])).
% 3.81/1.63  tff(c_1351, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1348, c_1300])).
% 3.81/1.63  tff(c_1354, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1291, c_1351])).
% 3.81/1.63  tff(c_1565, plain, (![D_209, C_210, B_211, A_212]: (m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(C_210, B_211))) | ~r1_tarski(k2_relat_1(D_209), B_211) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(C_210, A_212))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.63  tff(c_1567, plain, (![B_211]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_211))) | ~r1_tarski(k2_relat_1('#skF_4'), B_211))), inference(resolution, [status(thm)], [c_1263, c_1565])).
% 3.81/1.63  tff(c_1572, plain, (![B_213]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_213))))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1354, c_1567])).
% 3.81/1.63  tff(c_1587, plain, (![B_213]: (k1_relset_1('#skF_1', B_213, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1572, c_22])).
% 3.81/1.63  tff(c_1607, plain, (![B_213]: (k1_relset_1('#skF_1', B_213, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1587])).
% 3.81/1.63  tff(c_30, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.63  tff(c_1557, plain, (![C_24, B_23]: (v1_funct_2(C_24, '#skF_1', B_23) | k1_relset_1('#skF_1', B_23, C_24)!='#skF_1' | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_23))))), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1247, c_1247, c_1247, c_30])).
% 3.81/1.63  tff(c_1600, plain, (![B_213]: (v1_funct_2('#skF_4', '#skF_1', B_213) | k1_relset_1('#skF_1', B_213, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_1572, c_1557])).
% 3.81/1.63  tff(c_1623, plain, (![B_213]: (v1_funct_2('#skF_4', '#skF_1', B_213))), inference(demodulation, [status(thm), theory('equality')], [c_1607, c_1600])).
% 3.81/1.63  tff(c_1292, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.81/1.63  tff(c_1627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1292])).
% 3.81/1.63  tff(c_1628, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 3.81/1.63  tff(c_1938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1934, c_1628])).
% 3.81/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.63  
% 3.81/1.63  Inference rules
% 3.81/1.63  ----------------------
% 3.81/1.63  #Ref     : 0
% 3.81/1.63  #Sup     : 369
% 3.81/1.63  #Fact    : 0
% 3.81/1.63  #Define  : 0
% 3.81/1.63  #Split   : 7
% 3.81/1.63  #Chain   : 0
% 3.81/1.63  #Close   : 0
% 3.81/1.63  
% 3.81/1.63  Ordering : KBO
% 3.81/1.63  
% 3.81/1.63  Simplification rules
% 3.81/1.63  ----------------------
% 3.81/1.63  #Subsume      : 77
% 3.81/1.63  #Demod        : 417
% 3.81/1.63  #Tautology    : 180
% 3.81/1.63  #SimpNegUnit  : 4
% 3.81/1.63  #BackRed      : 59
% 3.81/1.63  
% 3.81/1.63  #Partial instantiations: 0
% 3.81/1.63  #Strategies tried      : 1
% 3.81/1.63  
% 3.81/1.63  Timing (in seconds)
% 3.81/1.63  ----------------------
% 3.81/1.64  Preprocessing        : 0.31
% 3.81/1.64  Parsing              : 0.16
% 3.81/1.64  CNF conversion       : 0.02
% 3.81/1.64  Main loop            : 0.50
% 3.81/1.64  Inferencing          : 0.18
% 3.81/1.64  Reduction            : 0.16
% 3.81/1.64  Demodulation         : 0.11
% 3.81/1.64  BG Simplification    : 0.02
% 3.81/1.64  Subsumption          : 0.10
% 3.81/1.64  Abstraction          : 0.02
% 3.81/1.64  MUC search           : 0.00
% 3.81/1.64  Cooper               : 0.00
% 3.81/1.64  Total                : 0.87
% 3.81/1.64  Index Insertion      : 0.00
% 3.81/1.64  Index Deletion       : 0.00
% 3.81/1.64  Index Matching       : 0.00
% 3.81/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
