%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:23 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 280 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 461 expanded)
%              Number of equality atoms :   38 ( 173 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_77,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1061,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1065,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1061])).

tff(c_44,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_557,plain,(
    ! [C_97,A_98,B_99,D_100] :
      ( r1_tarski(C_97,k1_relset_1(A_98,B_99,D_100))
      | ~ r1_tarski(k6_relat_1(C_97),D_100)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_583,plain,(
    ! [A_103,B_104] :
      ( r1_tarski('#skF_2',k1_relset_1(A_103,B_104,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(resolution,[status(thm)],[c_46,c_557])).

tff(c_586,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_583])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_586])).

tff(c_591,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1116,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_591])).

tff(c_18,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_649,plain,(
    ! [B_109,A_110] :
      ( v1_relat_1(B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_110))
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_652,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_649])).

tff(c_655,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_652])).

tff(c_16,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_825,plain,(
    ! [A_140,B_141] :
      ( r1_tarski(k2_relat_1(A_140),k2_relat_1(B_141))
      | ~ r1_tarski(A_140,B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_834,plain,(
    ! [A_21,B_141] :
      ( r1_tarski(A_21,k2_relat_1(B_141))
      | ~ r1_tarski(k6_relat_1(A_21),B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_825])).

tff(c_1048,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(A_154,k2_relat_1(B_155))
      | ~ r1_tarski(k6_relat_1(A_154),B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_834])).

tff(c_1057,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1048])).

tff(c_1060,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_1057])).

tff(c_24,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_683,plain,(
    ! [B_123,A_124] : k5_relat_1(k6_relat_1(B_123),k6_relat_1(A_124)) = k6_relat_1(k3_xboole_0(A_124,B_123)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_689,plain,(
    ! [A_124,B_123] :
      ( k7_relat_1(k6_relat_1(A_124),B_123) = k6_relat_1(k3_xboole_0(A_124,B_123))
      | ~ v1_relat_1(k6_relat_1(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_28])).

tff(c_699,plain,(
    ! [A_124,B_123] : k7_relat_1(k6_relat_1(A_124),B_123) = k6_relat_1(k3_xboole_0(A_124,B_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_689])).

tff(c_737,plain,(
    ! [B_134,A_135] :
      ( k7_relat_1(B_134,A_135) = B_134
      | ~ r1_tarski(k1_relat_1(B_134),A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_740,plain,(
    ! [A_21,A_135] :
      ( k7_relat_1(k6_relat_1(A_21),A_135) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_135)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_737])).

tff(c_743,plain,(
    ! [A_136,A_137] :
      ( k6_relat_1(k3_xboole_0(A_136,A_137)) = k6_relat_1(A_136)
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_699,c_740])).

tff(c_767,plain,(
    ! [A_136,A_137] :
      ( k3_xboole_0(A_136,A_137) = k1_relat_1(k6_relat_1(A_136))
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_24])).

tff(c_786,plain,(
    ! [A_136,A_137] :
      ( k3_xboole_0(A_136,A_137) = A_136
      | ~ r1_tarski(A_136,A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_767])).

tff(c_1073,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1060,c_786])).

tff(c_669,plain,(
    ! [C_118,B_119,A_120] :
      ( v5_relat_1(C_118,B_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_673,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_669])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_593,plain,(
    ! [B_105,A_106] : k1_setfam_1(k2_tarski(B_105,A_106)) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_599,plain,(
    ! [B_105,A_106] : k3_xboole_0(B_105,A_106) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_8])).

tff(c_778,plain,(
    ! [B_105,A_106] :
      ( k6_relat_1(k3_xboole_0(B_105,A_106)) = k6_relat_1(A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_743])).

tff(c_1077,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_778])).

tff(c_1121,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1077])).

tff(c_1127,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1121])).

tff(c_1134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_673,c_1127])).

tff(c_1136,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_864,plain,(
    ! [B_142,A_143] :
      ( k6_relat_1(k3_xboole_0(B_142,A_143)) = k6_relat_1(A_143)
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_743])).

tff(c_891,plain,(
    ! [B_142,A_143] :
      ( k3_xboole_0(B_142,A_143) = k1_relat_1(k6_relat_1(A_143))
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_24])).

tff(c_922,plain,(
    ! [B_142,A_143] :
      ( k3_xboole_0(B_142,A_143) = A_143
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_891])).

tff(c_1139,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1136,c_922])).

tff(c_1147,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1139])).

tff(c_1149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.45  
% 2.84/1.45  %Foreground sorts:
% 2.84/1.45  
% 2.84/1.45  
% 2.84/1.45  %Background operators:
% 2.84/1.45  
% 2.84/1.45  
% 2.84/1.45  %Foreground operators:
% 2.84/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.84/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.84/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.84/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.45  
% 3.16/1.47  tff(f_104, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 3.16/1.47  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.47  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 3.16/1.47  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.47  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.47  tff(f_48, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.16/1.47  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.16/1.47  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.16/1.47  tff(f_77, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.16/1.47  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.16/1.47  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.16/1.47  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.47  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.16/1.47  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.16/1.47  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.16/1.47  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.16/1.47  tff(c_1061, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.47  tff(c_1065, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1061])).
% 3.16/1.47  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.16/1.47  tff(c_126, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.16/1.47  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.16/1.47  tff(c_557, plain, (![C_97, A_98, B_99, D_100]: (r1_tarski(C_97, k1_relset_1(A_98, B_99, D_100)) | ~r1_tarski(k6_relat_1(C_97), D_100) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.47  tff(c_583, plain, (![A_103, B_104]: (r1_tarski('#skF_2', k1_relset_1(A_103, B_104, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(resolution, [status(thm)], [c_46, c_557])).
% 3.16/1.47  tff(c_586, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_583])).
% 3.16/1.47  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_586])).
% 3.16/1.47  tff(c_591, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.16/1.47  tff(c_1116, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_591])).
% 3.16/1.47  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.47  tff(c_649, plain, (![B_109, A_110]: (v1_relat_1(B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_110)) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.16/1.47  tff(c_652, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_649])).
% 3.16/1.47  tff(c_655, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_652])).
% 3.16/1.47  tff(c_16, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.47  tff(c_26, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.47  tff(c_825, plain, (![A_140, B_141]: (r1_tarski(k2_relat_1(A_140), k2_relat_1(B_141)) | ~r1_tarski(A_140, B_141) | ~v1_relat_1(B_141) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.47  tff(c_834, plain, (![A_21, B_141]: (r1_tarski(A_21, k2_relat_1(B_141)) | ~r1_tarski(k6_relat_1(A_21), B_141) | ~v1_relat_1(B_141) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_825])).
% 3.16/1.47  tff(c_1048, plain, (![A_154, B_155]: (r1_tarski(A_154, k2_relat_1(B_155)) | ~r1_tarski(k6_relat_1(A_154), B_155) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_834])).
% 3.16/1.47  tff(c_1057, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1048])).
% 3.16/1.47  tff(c_1060, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_655, c_1057])).
% 3.16/1.47  tff(c_24, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.47  tff(c_683, plain, (![B_123, A_124]: (k5_relat_1(k6_relat_1(B_123), k6_relat_1(A_124))=k6_relat_1(k3_xboole_0(A_124, B_123)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.47  tff(c_28, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.47  tff(c_689, plain, (![A_124, B_123]: (k7_relat_1(k6_relat_1(A_124), B_123)=k6_relat_1(k3_xboole_0(A_124, B_123)) | ~v1_relat_1(k6_relat_1(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_683, c_28])).
% 3.16/1.47  tff(c_699, plain, (![A_124, B_123]: (k7_relat_1(k6_relat_1(A_124), B_123)=k6_relat_1(k3_xboole_0(A_124, B_123)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_689])).
% 3.16/1.47  tff(c_737, plain, (![B_134, A_135]: (k7_relat_1(B_134, A_135)=B_134 | ~r1_tarski(k1_relat_1(B_134), A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.47  tff(c_740, plain, (![A_21, A_135]: (k7_relat_1(k6_relat_1(A_21), A_135)=k6_relat_1(A_21) | ~r1_tarski(A_21, A_135) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_737])).
% 3.16/1.47  tff(c_743, plain, (![A_136, A_137]: (k6_relat_1(k3_xboole_0(A_136, A_137))=k6_relat_1(A_136) | ~r1_tarski(A_136, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_699, c_740])).
% 3.16/1.47  tff(c_767, plain, (![A_136, A_137]: (k3_xboole_0(A_136, A_137)=k1_relat_1(k6_relat_1(A_136)) | ~r1_tarski(A_136, A_137))), inference(superposition, [status(thm), theory('equality')], [c_743, c_24])).
% 3.16/1.47  tff(c_786, plain, (![A_136, A_137]: (k3_xboole_0(A_136, A_137)=A_136 | ~r1_tarski(A_136, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_767])).
% 3.16/1.47  tff(c_1073, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_1060, c_786])).
% 3.16/1.47  tff(c_669, plain, (![C_118, B_119, A_120]: (v5_relat_1(C_118, B_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.47  tff(c_673, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_669])).
% 3.16/1.47  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.16/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.47  tff(c_111, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.47  tff(c_593, plain, (![B_105, A_106]: (k1_setfam_1(k2_tarski(B_105, A_106))=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_2, c_111])).
% 3.16/1.47  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.47  tff(c_599, plain, (![B_105, A_106]: (k3_xboole_0(B_105, A_106)=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_593, c_8])).
% 3.16/1.47  tff(c_778, plain, (![B_105, A_106]: (k6_relat_1(k3_xboole_0(B_105, A_106))=k6_relat_1(A_106) | ~r1_tarski(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_599, c_743])).
% 3.16/1.47  tff(c_1077, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1073, c_778])).
% 3.16/1.47  tff(c_1121, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1077])).
% 3.16/1.47  tff(c_1127, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1121])).
% 3.16/1.47  tff(c_1134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_655, c_673, c_1127])).
% 3.16/1.47  tff(c_1136, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1077])).
% 3.16/1.47  tff(c_864, plain, (![B_142, A_143]: (k6_relat_1(k3_xboole_0(B_142, A_143))=k6_relat_1(A_143) | ~r1_tarski(A_143, B_142))), inference(superposition, [status(thm), theory('equality')], [c_599, c_743])).
% 3.16/1.47  tff(c_891, plain, (![B_142, A_143]: (k3_xboole_0(B_142, A_143)=k1_relat_1(k6_relat_1(A_143)) | ~r1_tarski(A_143, B_142))), inference(superposition, [status(thm), theory('equality')], [c_864, c_24])).
% 3.16/1.47  tff(c_922, plain, (![B_142, A_143]: (k3_xboole_0(B_142, A_143)=A_143 | ~r1_tarski(A_143, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_891])).
% 3.16/1.47  tff(c_1139, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1136, c_922])).
% 3.16/1.47  tff(c_1147, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_1139])).
% 3.16/1.47  tff(c_1149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1116, c_1147])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 269
% 3.16/1.47  #Fact    : 0
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 5
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 16
% 3.16/1.47  #Demod        : 93
% 3.16/1.47  #Tautology    : 130
% 3.16/1.47  #SimpNegUnit  : 2
% 3.16/1.47  #BackRed      : 1
% 3.16/1.47  
% 3.16/1.47  #Partial instantiations: 0
% 3.16/1.47  #Strategies tried      : 1
% 3.16/1.47  
% 3.16/1.47  Timing (in seconds)
% 3.16/1.47  ----------------------
% 3.16/1.47  Preprocessing        : 0.32
% 3.16/1.47  Parsing              : 0.17
% 3.16/1.47  CNF conversion       : 0.02
% 3.16/1.47  Main loop            : 0.38
% 3.16/1.47  Inferencing          : 0.14
% 3.16/1.47  Reduction            : 0.13
% 3.16/1.47  Demodulation         : 0.10
% 3.16/1.47  BG Simplification    : 0.02
% 3.16/1.47  Subsumption          : 0.06
% 3.16/1.47  Abstraction          : 0.02
% 3.16/1.47  MUC search           : 0.00
% 3.16/1.47  Cooper               : 0.00
% 3.16/1.47  Total                : 0.73
% 3.16/1.47  Index Insertion      : 0.00
% 3.16/1.47  Index Deletion       : 0.00
% 3.16/1.47  Index Matching       : 0.00
% 3.16/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
