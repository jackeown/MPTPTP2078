%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 263 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 ( 459 expanded)
%              Number of equality atoms :   62 ( 135 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_76,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_22,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_736,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k8_relset_1(A_143,B_144,C_145,D_146) = k10_relat_1(C_145,D_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_739,plain,(
    ! [D_146] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_146) = k10_relat_1('#skF_3',D_146) ),
    inference(resolution,[status(thm)],[c_42,c_736])).

tff(c_578,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_582,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_578])).

tff(c_583,plain,(
    ! [B_119,A_120] :
      ( k7_relat_1(B_119,A_120) = B_119
      | ~ v4_relat_1(B_119,A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_586,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_582,c_583])).

tff(c_589,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_586])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_593,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_18])).

tff(c_597,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_593])).

tff(c_705,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k7_relset_1(A_138,B_139,C_140,D_141) = k9_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_708,plain,(
    ! [D_141] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_141) = k9_relat_1('#skF_3',D_141) ),
    inference(resolution,[status(thm)],[c_42,c_705])).

tff(c_668,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_672,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_668])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,(
    ! [D_90,B_91,C_92,A_93] :
      ( m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(B_91,C_92)))
      | ~ r1_tarski(k1_relat_1(D_90),B_91)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_93,C_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_274,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_94,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_94) ) ),
    inference(resolution,[status(thm)],[c_42,c_270])).

tff(c_28,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_307,plain,(
    ! [B_95] :
      ( v4_relat_1('#skF_3',B_95)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_95) ) ),
    inference(resolution,[status(thm)],[c_274,c_28])).

tff(c_312,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_307])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_315,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_312,c_24])).

tff(c_318,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_315])).

tff(c_325,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_18])).

tff(c_331,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_325])).

tff(c_129,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_133,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_124,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_128,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_134,plain,(
    ! [B_64,A_65] :
      ( k7_relat_1(B_64,A_65) = B_64
      | ~ v4_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_134])).

tff(c_140,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_137])).

tff(c_144,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_18])).

tff(c_148,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_144])).

tff(c_103,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k7_relat_1(B_56,A_57)) = k9_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_333,plain,(
    ! [B_96,A_97,A_98] :
      ( r1_tarski(k9_relat_1(B_96,A_97),A_98)
      | ~ v5_relat_1(k7_relat_1(B_96,A_97),A_98)
      | ~ v1_relat_1(k7_relat_1(B_96,A_97))
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_14])).

tff(c_342,plain,(
    ! [A_98] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_2'),A_98)
      | ~ v5_relat_1('#skF_3',A_98)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_333])).

tff(c_365,plain,(
    ! [A_99] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_99)
      | ~ v5_relat_1('#skF_3',A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_140,c_148,c_342])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_384,plain,(
    ! [A_100] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_100) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_100) ) ),
    inference(resolution,[status(thm)],[c_365,c_8])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k3_xboole_0(k2_relat_1(B_15),A_14)) = k10_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_393,plain,(
    ! [A_100] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_100)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_20])).

tff(c_501,plain,(
    ! [A_108] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_108)
      | ~ v5_relat_1('#skF_3',A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_393])).

tff(c_511,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_133,c_501])).

tff(c_520,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_22])).

tff(c_527,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_520])).

tff(c_255,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k7_relset_1(A_85,B_86,C_87,D_88) = k9_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [D_88] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_88) = k9_relat_1('#skF_3',D_88) ),
    inference(resolution,[status(thm)],[c_42,c_255])).

tff(c_215,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_relset_1(A_76,B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_218,plain,(
    ! [D_79] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_79) = k10_relat_1('#skF_3',D_79) ),
    inference(resolution,[status(thm)],[c_42,c_215])).

tff(c_196,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_200,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_196])).

tff(c_40,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_206,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_83])).

tff(c_219,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_206])).

tff(c_260,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_219])).

tff(c_532,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_260])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_532])).

tff(c_536,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_692,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_536])).

tff(c_709,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_692])).

tff(c_710,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_709])).

tff(c_741,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_710])).

tff(c_754,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_741])).

tff(c_758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.45  
% 2.78/1.45  %Foreground sorts:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Background operators:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Foreground operators:
% 2.78/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.45  
% 3.14/1.47  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.14/1.47  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.14/1.47  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.14/1.47  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.14/1.47  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.14/1.47  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.14/1.47  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.14/1.47  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.14/1.47  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.14/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.47  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.14/1.47  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.14/1.47  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.14/1.47  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.14/1.47  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.14/1.47  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.47  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.14/1.47  tff(c_76, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.47  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_76])).
% 3.14/1.47  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 3.14/1.47  tff(c_22, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.47  tff(c_736, plain, (![A_143, B_144, C_145, D_146]: (k8_relset_1(A_143, B_144, C_145, D_146)=k10_relat_1(C_145, D_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.47  tff(c_739, plain, (![D_146]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_146)=k10_relat_1('#skF_3', D_146))), inference(resolution, [status(thm)], [c_42, c_736])).
% 3.14/1.47  tff(c_578, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.47  tff(c_582, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_578])).
% 3.14/1.47  tff(c_583, plain, (![B_119, A_120]: (k7_relat_1(B_119, A_120)=B_119 | ~v4_relat_1(B_119, A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.47  tff(c_586, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_582, c_583])).
% 3.14/1.47  tff(c_589, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_586])).
% 3.14/1.47  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.47  tff(c_593, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_589, c_18])).
% 3.14/1.47  tff(c_597, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_593])).
% 3.14/1.47  tff(c_705, plain, (![A_138, B_139, C_140, D_141]: (k7_relset_1(A_138, B_139, C_140, D_141)=k9_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.47  tff(c_708, plain, (![D_141]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_141)=k9_relat_1('#skF_3', D_141))), inference(resolution, [status(thm)], [c_42, c_705])).
% 3.14/1.47  tff(c_668, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.14/1.47  tff(c_672, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_668])).
% 3.14/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.47  tff(c_270, plain, (![D_90, B_91, C_92, A_93]: (m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(B_91, C_92))) | ~r1_tarski(k1_relat_1(D_90), B_91) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_93, C_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.47  tff(c_274, plain, (![B_94]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_94, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_94))), inference(resolution, [status(thm)], [c_42, c_270])).
% 3.14/1.47  tff(c_28, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.47  tff(c_307, plain, (![B_95]: (v4_relat_1('#skF_3', B_95) | ~r1_tarski(k1_relat_1('#skF_3'), B_95))), inference(resolution, [status(thm)], [c_274, c_28])).
% 3.14/1.47  tff(c_312, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_307])).
% 3.14/1.47  tff(c_24, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.47  tff(c_315, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_312, c_24])).
% 3.14/1.47  tff(c_318, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_315])).
% 3.14/1.47  tff(c_325, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_318, c_18])).
% 3.14/1.47  tff(c_331, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_325])).
% 3.14/1.47  tff(c_129, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.47  tff(c_133, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_129])).
% 3.14/1.47  tff(c_124, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.47  tff(c_128, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_124])).
% 3.14/1.47  tff(c_134, plain, (![B_64, A_65]: (k7_relat_1(B_64, A_65)=B_64 | ~v4_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.47  tff(c_137, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_134])).
% 3.14/1.47  tff(c_140, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_137])).
% 3.14/1.47  tff(c_144, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_18])).
% 3.14/1.47  tff(c_148, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_144])).
% 3.14/1.47  tff(c_103, plain, (![B_56, A_57]: (k2_relat_1(k7_relat_1(B_56, A_57))=k9_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.47  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.47  tff(c_333, plain, (![B_96, A_97, A_98]: (r1_tarski(k9_relat_1(B_96, A_97), A_98) | ~v5_relat_1(k7_relat_1(B_96, A_97), A_98) | ~v1_relat_1(k7_relat_1(B_96, A_97)) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_103, c_14])).
% 3.14/1.47  tff(c_342, plain, (![A_98]: (r1_tarski(k9_relat_1('#skF_3', '#skF_2'), A_98) | ~v5_relat_1('#skF_3', A_98) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_333])).
% 3.14/1.47  tff(c_365, plain, (![A_99]: (r1_tarski(k2_relat_1('#skF_3'), A_99) | ~v5_relat_1('#skF_3', A_99))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_140, c_148, c_342])).
% 3.14/1.47  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.47  tff(c_384, plain, (![A_100]: (k3_xboole_0(k2_relat_1('#skF_3'), A_100)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_100))), inference(resolution, [status(thm)], [c_365, c_8])).
% 3.14/1.47  tff(c_20, plain, (![B_15, A_14]: (k10_relat_1(B_15, k3_xboole_0(k2_relat_1(B_15), A_14))=k10_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.14/1.47  tff(c_393, plain, (![A_100]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_100) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_100))), inference(superposition, [status(thm), theory('equality')], [c_384, c_20])).
% 3.14/1.47  tff(c_501, plain, (![A_108]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_108) | ~v5_relat_1('#skF_3', A_108))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_393])).
% 3.14/1.47  tff(c_511, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_133, c_501])).
% 3.14/1.47  tff(c_520, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_22])).
% 3.14/1.47  tff(c_527, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_520])).
% 3.14/1.47  tff(c_255, plain, (![A_85, B_86, C_87, D_88]: (k7_relset_1(A_85, B_86, C_87, D_88)=k9_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.14/1.47  tff(c_258, plain, (![D_88]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_88)=k9_relat_1('#skF_3', D_88))), inference(resolution, [status(thm)], [c_42, c_255])).
% 3.14/1.47  tff(c_215, plain, (![A_76, B_77, C_78, D_79]: (k8_relset_1(A_76, B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.47  tff(c_218, plain, (![D_79]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_79)=k10_relat_1('#skF_3', D_79))), inference(resolution, [status(thm)], [c_42, c_215])).
% 3.14/1.47  tff(c_196, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.14/1.47  tff(c_200, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_196])).
% 3.14/1.47  tff(c_40, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.14/1.47  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.14/1.47  tff(c_206, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_83])).
% 3.14/1.47  tff(c_219, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_218, c_206])).
% 3.14/1.47  tff(c_260, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_219])).
% 3.14/1.47  tff(c_532, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_260])).
% 3.14/1.47  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_331, c_532])).
% 3.14/1.47  tff(c_536, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.14/1.47  tff(c_692, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_536])).
% 3.14/1.47  tff(c_709, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_708, c_692])).
% 3.14/1.47  tff(c_710, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_709])).
% 3.14/1.47  tff(c_741, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_710])).
% 3.14/1.47  tff(c_754, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_741])).
% 3.14/1.47  tff(c_758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_754])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 162
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 1
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 3
% 3.14/1.47  #Demod        : 87
% 3.14/1.47  #Tautology    : 91
% 3.14/1.47  #SimpNegUnit  : 0
% 3.14/1.47  #BackRed      : 12
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.36
% 3.14/1.47  Parsing              : 0.20
% 3.14/1.47  CNF conversion       : 0.02
% 3.14/1.47  Main loop            : 0.33
% 3.14/1.47  Inferencing          : 0.13
% 3.14/1.47  Reduction            : 0.10
% 3.14/1.47  Demodulation         : 0.08
% 3.14/1.47  BG Simplification    : 0.02
% 3.14/1.47  Subsumption          : 0.05
% 3.14/1.47  Abstraction          : 0.02
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.73
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
