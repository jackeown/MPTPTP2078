%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 141 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 220 expanded)
%              Number of equality atoms :   59 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_16,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1393,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k8_relset_1(A_178,B_179,C_180,D_181) = k10_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1396,plain,(
    ! [D_181] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_181) = k10_relat_1('#skF_3',D_181) ),
    inference(resolution,[status(thm)],[c_46,c_1393])).

tff(c_827,plain,(
    ! [C_133,A_134,B_135] :
      ( v4_relat_1(C_133,A_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_831,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_827])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_834,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_831,c_20])).

tff(c_837,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_834])).

tff(c_842,plain,(
    ! [B_136,A_137] :
      ( k2_relat_1(k7_relat_1(B_136,A_137)) = k9_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_863,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_842])).

tff(c_867,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_863])).

tff(c_1348,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k7_relset_1(A_171,B_172,C_173,D_174) = k9_relat_1(C_173,D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1351,plain,(
    ! [D_174] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_174) = k9_relat_1('#skF_3',D_174) ),
    inference(resolution,[status(thm)],[c_46,c_1348])).

tff(c_1216,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1220,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1216])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ r1_tarski(k1_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_215,plain,(
    ! [B_72] :
      ( k7_relat_1(B_72,k1_relat_1(B_72)) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [B_72] :
      ( k9_relat_1(B_72,k1_relat_1(B_72)) = k2_relat_1(B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_14])).

tff(c_117,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_121,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [B_74,A_75] :
      ( k5_relat_1(B_74,k6_relat_1(A_75)) = B_74
      | ~ r1_tarski(k2_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_260,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_246])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_451,plain,(
    ! [A_90,B_91] :
      ( k10_relat_1(A_90,k1_relat_1(B_91)) = k1_relat_1(k5_relat_1(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_468,plain,(
    ! [A_90,A_14] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_14))) = k10_relat_1(A_90,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_451])).

tff(c_477,plain,(
    ! [A_92,A_93] :
      ( k1_relat_1(k5_relat_1(A_92,k6_relat_1(A_93))) = k10_relat_1(A_92,A_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_468])).

tff(c_708,plain,(
    ! [B_110,A_111] :
      ( k10_relat_1(B_110,A_111) = k1_relat_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v5_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_477])).

tff(c_720,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_708])).

tff(c_730,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_720])).

tff(c_735,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k8_relset_1(A_112,B_113,C_114,D_115) = k10_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_738,plain,(
    ! [D_115] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_115) = k10_relat_1('#skF_3',D_115) ),
    inference(resolution,[status(thm)],[c_46,c_735])).

tff(c_675,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k7_relset_1(A_103,B_104,C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_678,plain,(
    ! [D_106] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_106) = k9_relat_1('#skF_3',D_106) ),
    inference(resolution,[status(thm)],[c_46,c_675])).

tff(c_645,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_649,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_645])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_94,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_650,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_94])).

tff(c_679,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_650])).

tff(c_739,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_679])).

tff(c_740,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_739])).

tff(c_752,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_740])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_752])).

tff(c_757,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1221,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_757])).

tff(c_1352,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1351,c_1221])).

tff(c_1353,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_1352])).

tff(c_1398,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1353])).

tff(c_1411,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1398])).

tff(c_1415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.48  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.48  
% 3.09/1.48  %Foreground sorts:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Background operators:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Foreground operators:
% 3.09/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.09/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.09/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.09/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.09/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.09/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.48  
% 3.09/1.50  tff(f_109, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.09/1.50  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.09/1.50  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.09/1.50  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.09/1.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.50  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.09/1.50  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.09/1.50  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.09/1.50  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.09/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.50  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.09/1.50  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.09/1.50  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.09/1.50  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.09/1.50  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.09/1.50  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.09/1.50  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.09/1.50  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.50  tff(c_68, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.50  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.09/1.50  tff(c_16, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.50  tff(c_1393, plain, (![A_178, B_179, C_180, D_181]: (k8_relset_1(A_178, B_179, C_180, D_181)=k10_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.09/1.50  tff(c_1396, plain, (![D_181]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_181)=k10_relat_1('#skF_3', D_181))), inference(resolution, [status(thm)], [c_46, c_1393])).
% 3.09/1.50  tff(c_827, plain, (![C_133, A_134, B_135]: (v4_relat_1(C_133, A_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.50  tff(c_831, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_827])).
% 3.09/1.50  tff(c_20, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.09/1.50  tff(c_834, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_831, c_20])).
% 3.09/1.50  tff(c_837, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_834])).
% 3.09/1.50  tff(c_842, plain, (![B_136, A_137]: (k2_relat_1(k7_relat_1(B_136, A_137))=k9_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.50  tff(c_863, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_837, c_842])).
% 3.09/1.50  tff(c_867, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_863])).
% 3.09/1.50  tff(c_1348, plain, (![A_171, B_172, C_173, D_174]: (k7_relset_1(A_171, B_172, C_173, D_174)=k9_relat_1(C_173, D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.09/1.50  tff(c_1351, plain, (![D_174]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_174)=k9_relat_1('#skF_3', D_174))), inference(resolution, [status(thm)], [c_46, c_1348])).
% 3.09/1.50  tff(c_1216, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.09/1.50  tff(c_1220, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1216])).
% 3.09/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.50  tff(c_199, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~r1_tarski(k1_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.09/1.50  tff(c_215, plain, (![B_72]: (k7_relat_1(B_72, k1_relat_1(B_72))=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_199])).
% 3.09/1.50  tff(c_14, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.50  tff(c_221, plain, (![B_72]: (k9_relat_1(B_72, k1_relat_1(B_72))=k2_relat_1(B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_215, c_14])).
% 3.09/1.50  tff(c_117, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.50  tff(c_121, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_117])).
% 3.09/1.50  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.50  tff(c_246, plain, (![B_74, A_75]: (k5_relat_1(B_74, k6_relat_1(A_75))=B_74 | ~r1_tarski(k2_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.50  tff(c_260, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_246])).
% 3.09/1.50  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.50  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.09/1.50  tff(c_451, plain, (![A_90, B_91]: (k10_relat_1(A_90, k1_relat_1(B_91))=k1_relat_1(k5_relat_1(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.50  tff(c_468, plain, (![A_90, A_14]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_14)))=k10_relat_1(A_90, A_14) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_22, c_451])).
% 3.09/1.50  tff(c_477, plain, (![A_92, A_93]: (k1_relat_1(k5_relat_1(A_92, k6_relat_1(A_93)))=k10_relat_1(A_92, A_93) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_468])).
% 3.09/1.50  tff(c_708, plain, (![B_110, A_111]: (k10_relat_1(B_110, A_111)=k1_relat_1(B_110) | ~v1_relat_1(B_110) | ~v5_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_260, c_477])).
% 3.09/1.50  tff(c_720, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_708])).
% 3.09/1.50  tff(c_730, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_720])).
% 3.09/1.50  tff(c_735, plain, (![A_112, B_113, C_114, D_115]: (k8_relset_1(A_112, B_113, C_114, D_115)=k10_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.09/1.50  tff(c_738, plain, (![D_115]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_115)=k10_relat_1('#skF_3', D_115))), inference(resolution, [status(thm)], [c_46, c_735])).
% 3.09/1.50  tff(c_675, plain, (![A_103, B_104, C_105, D_106]: (k7_relset_1(A_103, B_104, C_105, D_106)=k9_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.09/1.50  tff(c_678, plain, (![D_106]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_106)=k9_relat_1('#skF_3', D_106))), inference(resolution, [status(thm)], [c_46, c_675])).
% 3.09/1.50  tff(c_645, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.09/1.50  tff(c_649, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_645])).
% 3.09/1.50  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.50  tff(c_94, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.09/1.50  tff(c_650, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_649, c_94])).
% 3.09/1.50  tff(c_679, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_650])).
% 3.09/1.50  tff(c_739, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_679])).
% 3.09/1.50  tff(c_740, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_739])).
% 3.09/1.50  tff(c_752, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_221, c_740])).
% 3.09/1.50  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_752])).
% 3.09/1.50  tff(c_757, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.09/1.50  tff(c_1221, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_757])).
% 3.09/1.50  tff(c_1352, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1351, c_1221])).
% 3.09/1.50  tff(c_1353, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_867, c_1352])).
% 3.09/1.50  tff(c_1398, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1353])).
% 3.09/1.50  tff(c_1411, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1398])).
% 3.09/1.50  tff(c_1415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1411])).
% 3.09/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.50  
% 3.09/1.50  Inference rules
% 3.09/1.50  ----------------------
% 3.09/1.50  #Ref     : 0
% 3.09/1.50  #Sup     : 289
% 3.09/1.50  #Fact    : 0
% 3.09/1.50  #Define  : 0
% 3.09/1.50  #Split   : 1
% 3.09/1.50  #Chain   : 0
% 3.09/1.50  #Close   : 0
% 3.09/1.50  
% 3.09/1.50  Ordering : KBO
% 3.09/1.50  
% 3.09/1.50  Simplification rules
% 3.09/1.50  ----------------------
% 3.09/1.50  #Subsume      : 8
% 3.09/1.50  #Demod        : 237
% 3.09/1.50  #Tautology    : 178
% 3.09/1.50  #SimpNegUnit  : 0
% 3.09/1.50  #BackRed      : 9
% 3.09/1.50  
% 3.09/1.50  #Partial instantiations: 0
% 3.09/1.50  #Strategies tried      : 1
% 3.09/1.50  
% 3.09/1.50  Timing (in seconds)
% 3.09/1.50  ----------------------
% 3.09/1.50  Preprocessing        : 0.32
% 3.09/1.50  Parsing              : 0.17
% 3.09/1.50  CNF conversion       : 0.02
% 3.09/1.50  Main loop            : 0.40
% 3.09/1.50  Inferencing          : 0.16
% 3.09/1.50  Reduction            : 0.13
% 3.09/1.50  Demodulation         : 0.10
% 3.09/1.50  BG Simplification    : 0.02
% 3.09/1.50  Subsumption          : 0.06
% 3.09/1.50  Abstraction          : 0.03
% 3.09/1.50  MUC search           : 0.00
% 3.09/1.50  Cooper               : 0.00
% 3.09/1.50  Total                : 0.75
% 3.09/1.50  Index Insertion      : 0.00
% 3.09/1.50  Index Deletion       : 0.00
% 3.09/1.50  Index Matching       : 0.00
% 3.09/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
