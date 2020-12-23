%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 898 expanded)
%              Number of leaves         :   38 ( 324 expanded)
%              Depth                    :   18
%              Number of atoms          :  261 (2613 expanded)
%              Number of equality atoms :   45 ( 375 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_60,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_118,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_237,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_244,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_237])).

tff(c_247,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_244])).

tff(c_191,plain,(
    ! [A_63] :
      ( k1_relat_1(k2_funct_1(A_63)) = k2_relat_1(A_63)
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(B_59,A_60)
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    ! [B_59] :
      ( v4_relat_1(B_59,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_561,plain,(
    ! [A_130] :
      ( v4_relat_1(k2_funct_1(A_130),k2_relat_1(A_130))
      | ~ v1_relat_1(k2_funct_1(A_130))
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_167])).

tff(c_569,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_561])).

tff(c_579,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_569])).

tff(c_580,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_579])).

tff(c_583,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_580])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_583])).

tff(c_589,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_588,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_579])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_594,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_588,c_22])).

tff(c_600,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_594])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_605,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_20])).

tff(c_609,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_605])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k9_relat_1(k2_funct_1(B_18),A_17) = k10_relat_1(B_18,A_17)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_614,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_28])).

tff(c_621,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_614])).

tff(c_30,plain,(
    ! [A_19] :
      ( k2_relat_1(k2_funct_1(A_19)) = k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_651,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_30])).

tff(c_662,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_651])).

tff(c_313,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k8_relset_1(A_82,B_83,C_84,D_85) = k10_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_320,plain,(
    ! [D_85] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_85) = k10_relat_1('#skF_3',D_85) ),
    inference(resolution,[status(thm)],[c_52,c_313])).

tff(c_343,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( m1_subset_1(k8_relset_1(A_91,B_92,C_93,D_94),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_359,plain,(
    ! [D_85] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_85),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_343])).

tff(c_366,plain,(
    ! [D_95] : m1_subset_1(k10_relat_1('#skF_3',D_95),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_359])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    ! [D_95] : r1_tarski(k10_relat_1('#skF_3',D_95),'#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_8])).

tff(c_672,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_374])).

tff(c_67,plain,(
    ! [A_39] :
      ( v1_funct_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_70,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_66])).

tff(c_73,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_70])).

tff(c_83,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_83])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_93])).

tff(c_97,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_666,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_621])).

tff(c_32,plain,(
    ! [A_19] :
      ( k1_relat_1(k2_funct_1(A_19)) = k2_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_384,plain,(
    ! [B_97,A_98] :
      ( m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97),A_98)))
      | ~ r1_tarski(k2_relat_1(B_97),A_98)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1221,plain,(
    ! [A_161,A_162] :
      ( m1_subset_1(k2_funct_1(A_161),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_161),A_162)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_161)),A_162)
      | ~ v1_funct_1(k2_funct_1(A_161))
      | ~ v1_relat_1(k2_funct_1(A_161))
      | ~ v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_384])).

tff(c_1242,plain,(
    ! [A_162] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_162)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_162)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_1221])).

tff(c_1273,plain,(
    ! [A_164] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_164)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_589,c_97,c_666,c_1242])).

tff(c_96,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_173,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_1285,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1273,c_173])).

tff(c_1300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_1285])).

tff(c_1302,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1305,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1302,c_12])).

tff(c_1311,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1305])).

tff(c_1382,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1392,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1382])).

tff(c_1396,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1392])).

tff(c_1335,plain,(
    ! [A_166] :
      ( k1_relat_1(k2_funct_1(A_166)) = k2_relat_1(A_166)
      | ~ v2_funct_1(A_166)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1796,plain,(
    ! [A_239] :
      ( v4_relat_1(k2_funct_1(A_239),k2_relat_1(A_239))
      | ~ v1_relat_1(k2_funct_1(A_239))
      | ~ v2_funct_1(A_239)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_167])).

tff(c_1804,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_1796])).

tff(c_1814,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_1311,c_1804])).

tff(c_1819,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1814,c_22])).

tff(c_1825,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1819])).

tff(c_1829,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1825,c_20])).

tff(c_1833,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1311,c_1829])).

tff(c_1838,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1833,c_28])).

tff(c_1845,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_1838])).

tff(c_1857,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1845,c_30])).

tff(c_1866,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_1857])).

tff(c_1517,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k8_relset_1(A_195,B_196,C_197,D_198) = k10_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1531,plain,(
    ! [D_198] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_198) = k10_relat_1('#skF_3',D_198) ),
    inference(resolution,[status(thm)],[c_52,c_1517])).

tff(c_1471,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( m1_subset_1(k8_relset_1(A_185,B_186,C_187,D_188),k1_zfmisc_1(A_185))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1485,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( r1_tarski(k8_relset_1(A_189,B_190,C_191,D_192),A_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(resolution,[status(thm)],[c_1471,c_8])).

tff(c_1499,plain,(
    ! [D_192] : r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_3',D_192),'#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1485])).

tff(c_1532,plain,(
    ! [D_192] : r1_tarski(k10_relat_1('#skF_3',D_192),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1531,c_1499])).

tff(c_1878,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_1532])).

tff(c_1870,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_1845])).

tff(c_1467,plain,(
    ! [B_183,A_184] :
      ( v1_funct_2(B_183,k1_relat_1(B_183),A_184)
      | ~ r1_tarski(k2_relat_1(B_183),A_184)
      | ~ v1_funct_1(B_183)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2332,plain,(
    ! [A_264,A_265] :
      ( v1_funct_2(k2_funct_1(A_264),k2_relat_1(A_264),A_265)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_264)),A_265)
      | ~ v1_funct_1(k2_funct_1(A_264))
      | ~ v1_relat_1(k2_funct_1(A_264))
      | ~ v2_funct_1(A_264)
      | ~ v1_funct_1(A_264)
      | ~ v1_relat_1(A_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1467])).

tff(c_2338,plain,(
    ! [A_265] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_265)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_265)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_2332])).

tff(c_2349,plain,(
    ! [A_266] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_266)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_56,c_50,c_1311,c_97,c_1870,c_2338])).

tff(c_1301,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2352,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2349,c_1301])).

tff(c_2356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_2352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.82  
% 4.40/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.82  %$ v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.40/1.82  
% 4.40/1.82  %Foreground sorts:
% 4.40/1.82  
% 4.40/1.82  
% 4.40/1.82  %Background operators:
% 4.40/1.82  
% 4.40/1.82  
% 4.40/1.82  %Foreground operators:
% 4.40/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.40/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.40/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.40/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.40/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.40/1.82  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.40/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.40/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.40/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.40/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.40/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.40/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.40/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.40/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.40/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.40/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.40/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.40/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.40/1.82  
% 4.52/1.84  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.52/1.84  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.52/1.84  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.52/1.84  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.52/1.84  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.52/1.84  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.52/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.52/1.84  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.52/1.84  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.52/1.84  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.52/1.84  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 4.52/1.84  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.52/1.84  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 4.52/1.84  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.52/1.84  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.52/1.84  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.52/1.84  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.52/1.84  tff(c_118, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.84  tff(c_124, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_118])).
% 4.52/1.84  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_124])).
% 4.52/1.84  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.52/1.84  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.52/1.84  tff(c_26, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.84  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.52/1.84  tff(c_237, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.52/1.84  tff(c_244, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_237])).
% 4.52/1.84  tff(c_247, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_244])).
% 4.52/1.84  tff(c_191, plain, (![A_63]: (k1_relat_1(k2_funct_1(A_63))=k2_relat_1(A_63) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.52/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.84  tff(c_158, plain, (![B_59, A_60]: (v4_relat_1(B_59, A_60) | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.52/1.84  tff(c_167, plain, (![B_59]: (v4_relat_1(B_59, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_158])).
% 4.52/1.84  tff(c_561, plain, (![A_130]: (v4_relat_1(k2_funct_1(A_130), k2_relat_1(A_130)) | ~v1_relat_1(k2_funct_1(A_130)) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_191, c_167])).
% 4.52/1.84  tff(c_569, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_247, c_561])).
% 4.52/1.84  tff(c_579, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_569])).
% 4.52/1.84  tff(c_580, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_579])).
% 4.52/1.84  tff(c_583, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_580])).
% 4.52/1.84  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_583])).
% 4.52/1.84  tff(c_589, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_579])).
% 4.52/1.84  tff(c_588, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_579])).
% 4.52/1.84  tff(c_22, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.52/1.84  tff(c_594, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_588, c_22])).
% 4.52/1.84  tff(c_600, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_594])).
% 4.52/1.84  tff(c_20, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.52/1.84  tff(c_605, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_20])).
% 4.52/1.84  tff(c_609, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_605])).
% 4.52/1.84  tff(c_28, plain, (![B_18, A_17]: (k9_relat_1(k2_funct_1(B_18), A_17)=k10_relat_1(B_18, A_17) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.52/1.84  tff(c_614, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_609, c_28])).
% 4.52/1.84  tff(c_621, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_614])).
% 4.52/1.84  tff(c_30, plain, (![A_19]: (k2_relat_1(k2_funct_1(A_19))=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.52/1.84  tff(c_651, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_621, c_30])).
% 4.52/1.84  tff(c_662, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_651])).
% 4.52/1.84  tff(c_313, plain, (![A_82, B_83, C_84, D_85]: (k8_relset_1(A_82, B_83, C_84, D_85)=k10_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.52/1.84  tff(c_320, plain, (![D_85]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_85)=k10_relat_1('#skF_3', D_85))), inference(resolution, [status(thm)], [c_52, c_313])).
% 4.52/1.84  tff(c_343, plain, (![A_91, B_92, C_93, D_94]: (m1_subset_1(k8_relset_1(A_91, B_92, C_93, D_94), k1_zfmisc_1(A_91)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.52/1.84  tff(c_359, plain, (![D_85]: (m1_subset_1(k10_relat_1('#skF_3', D_85), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_320, c_343])).
% 4.52/1.84  tff(c_366, plain, (![D_95]: (m1_subset_1(k10_relat_1('#skF_3', D_95), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_359])).
% 4.52/1.84  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.84  tff(c_374, plain, (![D_95]: (r1_tarski(k10_relat_1('#skF_3', D_95), '#skF_1'))), inference(resolution, [status(thm)], [c_366, c_8])).
% 4.52/1.84  tff(c_672, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_662, c_374])).
% 4.52/1.84  tff(c_67, plain, (![A_39]: (v1_funct_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.52/1.84  tff(c_46, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.52/1.84  tff(c_66, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.52/1.84  tff(c_70, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_66])).
% 4.52/1.84  tff(c_73, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_70])).
% 4.52/1.84  tff(c_83, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.84  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_83])).
% 4.52/1.84  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_89])).
% 4.52/1.84  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_93])).
% 4.52/1.84  tff(c_97, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 4.52/1.84  tff(c_666, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_662, c_621])).
% 4.52/1.84  tff(c_32, plain, (![A_19]: (k1_relat_1(k2_funct_1(A_19))=k2_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.52/1.84  tff(c_384, plain, (![B_97, A_98]: (m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_97), A_98))) | ~r1_tarski(k2_relat_1(B_97), A_98) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.84  tff(c_1221, plain, (![A_161, A_162]: (m1_subset_1(k2_funct_1(A_161), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_161), A_162))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_161)), A_162) | ~v1_funct_1(k2_funct_1(A_161)) | ~v1_relat_1(k2_funct_1(A_161)) | ~v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_32, c_384])).
% 4.52/1.84  tff(c_1242, plain, (![A_162]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_162))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_162) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_1221])).
% 4.52/1.84  tff(c_1273, plain, (![A_164]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_164))) | ~r1_tarski(k1_relat_1('#skF_3'), A_164))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_589, c_97, c_666, c_1242])).
% 4.52/1.84  tff(c_96, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_46])).
% 4.52/1.84  tff(c_173, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_96])).
% 4.52/1.84  tff(c_1285, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1273, c_173])).
% 4.52/1.84  tff(c_1300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_672, c_1285])).
% 4.52/1.84  tff(c_1302, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_96])).
% 4.52/1.84  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.84  tff(c_1305, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_1302, c_12])).
% 4.52/1.84  tff(c_1311, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1305])).
% 4.52/1.84  tff(c_1382, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.52/1.84  tff(c_1392, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1382])).
% 4.52/1.84  tff(c_1396, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1392])).
% 4.52/1.84  tff(c_1335, plain, (![A_166]: (k1_relat_1(k2_funct_1(A_166))=k2_relat_1(A_166) | ~v2_funct_1(A_166) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.52/1.84  tff(c_1796, plain, (![A_239]: (v4_relat_1(k2_funct_1(A_239), k2_relat_1(A_239)) | ~v1_relat_1(k2_funct_1(A_239)) | ~v2_funct_1(A_239) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_167])).
% 4.52/1.84  tff(c_1804, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1396, c_1796])).
% 4.52/1.84  tff(c_1814, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_1311, c_1804])).
% 4.52/1.84  tff(c_1819, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1814, c_22])).
% 4.52/1.84  tff(c_1825, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1819])).
% 4.52/1.84  tff(c_1829, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1825, c_20])).
% 4.52/1.84  tff(c_1833, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1311, c_1829])).
% 4.52/1.84  tff(c_1838, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1833, c_28])).
% 4.52/1.84  tff(c_1845, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_1838])).
% 4.52/1.84  tff(c_1857, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1845, c_30])).
% 4.52/1.84  tff(c_1866, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_1857])).
% 4.52/1.84  tff(c_1517, plain, (![A_195, B_196, C_197, D_198]: (k8_relset_1(A_195, B_196, C_197, D_198)=k10_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.52/1.84  tff(c_1531, plain, (![D_198]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_198)=k10_relat_1('#skF_3', D_198))), inference(resolution, [status(thm)], [c_52, c_1517])).
% 4.52/1.84  tff(c_1471, plain, (![A_185, B_186, C_187, D_188]: (m1_subset_1(k8_relset_1(A_185, B_186, C_187, D_188), k1_zfmisc_1(A_185)) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.52/1.84  tff(c_1485, plain, (![A_189, B_190, C_191, D_192]: (r1_tarski(k8_relset_1(A_189, B_190, C_191, D_192), A_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(resolution, [status(thm)], [c_1471, c_8])).
% 4.52/1.84  tff(c_1499, plain, (![D_192]: (r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_192), '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_1485])).
% 4.52/1.84  tff(c_1532, plain, (![D_192]: (r1_tarski(k10_relat_1('#skF_3', D_192), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1531, c_1499])).
% 4.52/1.84  tff(c_1878, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_1532])).
% 4.52/1.84  tff(c_1870, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_1845])).
% 4.52/1.84  tff(c_1467, plain, (![B_183, A_184]: (v1_funct_2(B_183, k1_relat_1(B_183), A_184) | ~r1_tarski(k2_relat_1(B_183), A_184) | ~v1_funct_1(B_183) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.52/1.84  tff(c_2332, plain, (![A_264, A_265]: (v1_funct_2(k2_funct_1(A_264), k2_relat_1(A_264), A_265) | ~r1_tarski(k2_relat_1(k2_funct_1(A_264)), A_265) | ~v1_funct_1(k2_funct_1(A_264)) | ~v1_relat_1(k2_funct_1(A_264)) | ~v2_funct_1(A_264) | ~v1_funct_1(A_264) | ~v1_relat_1(A_264))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1467])).
% 4.52/1.84  tff(c_2338, plain, (![A_265]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_265) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_265) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_2332])).
% 4.52/1.84  tff(c_2349, plain, (![A_266]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_266) | ~r1_tarski(k1_relat_1('#skF_3'), A_266))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_56, c_50, c_1311, c_97, c_1870, c_2338])).
% 4.52/1.84  tff(c_1301, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 4.52/1.84  tff(c_2352, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2349, c_1301])).
% 4.52/1.84  tff(c_2356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1878, c_2352])).
% 4.52/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.84  
% 4.52/1.84  Inference rules
% 4.52/1.84  ----------------------
% 4.52/1.85  #Ref     : 0
% 4.52/1.85  #Sup     : 528
% 4.52/1.85  #Fact    : 0
% 4.52/1.85  #Define  : 0
% 4.52/1.85  #Split   : 21
% 4.52/1.85  #Chain   : 0
% 4.52/1.85  #Close   : 0
% 4.52/1.85  
% 4.52/1.85  Ordering : KBO
% 4.52/1.85  
% 4.52/1.85  Simplification rules
% 4.52/1.85  ----------------------
% 4.52/1.85  #Subsume      : 50
% 4.52/1.85  #Demod        : 366
% 4.52/1.85  #Tautology    : 214
% 4.52/1.85  #SimpNegUnit  : 3
% 4.52/1.85  #BackRed      : 7
% 4.52/1.85  
% 4.52/1.85  #Partial instantiations: 0
% 4.52/1.85  #Strategies tried      : 1
% 4.52/1.85  
% 4.52/1.85  Timing (in seconds)
% 4.52/1.85  ----------------------
% 4.52/1.85  Preprocessing        : 0.35
% 4.52/1.85  Parsing              : 0.19
% 4.52/1.85  CNF conversion       : 0.02
% 4.52/1.85  Main loop            : 0.66
% 4.52/1.85  Inferencing          : 0.24
% 4.52/1.85  Reduction            : 0.22
% 4.52/1.85  Demodulation         : 0.16
% 4.52/1.85  BG Simplification    : 0.03
% 4.52/1.85  Subsumption          : 0.11
% 4.52/1.85  Abstraction          : 0.03
% 4.52/1.85  MUC search           : 0.00
% 4.52/1.85  Cooper               : 0.00
% 4.52/1.85  Total                : 1.05
% 4.52/1.85  Index Insertion      : 0.00
% 4.52/1.85  Index Deletion       : 0.00
% 4.52/1.85  Index Matching       : 0.00
% 4.52/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
