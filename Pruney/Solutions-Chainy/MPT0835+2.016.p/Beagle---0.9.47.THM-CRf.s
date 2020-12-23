%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:57 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 134 expanded)
%              Number of leaves         :   40 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 204 expanded)
%              Number of equality atoms :   54 (  86 expanded)
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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_12,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_544,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_548,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_544])).

tff(c_554,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = B_116
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_557,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_548,c_554])).

tff(c_560,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_557])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_564,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_10])).

tff(c_568,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_564])).

tff(c_927,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k7_relset_1(A_147,B_148,C_149,D_150) = k9_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_930,plain,(
    ! [D_150] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_150) = k9_relat_1('#skF_3',D_150) ),
    inference(resolution,[status(thm)],[c_40,c_927])).

tff(c_907,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_910,plain,(
    ! [D_145] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_145) = k10_relat_1('#skF_3',D_145) ),
    inference(resolution,[status(thm)],[c_40,c_907])).

tff(c_596,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_600,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_596])).

tff(c_8,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [B_64,A_65] :
      ( k5_relat_1(B_64,k6_relat_1(A_65)) = B_64
      | ~ r1_tarski(k2_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_192,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_182])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_245,plain,(
    ! [A_76,B_77] :
      ( k10_relat_1(A_76,k1_relat_1(B_77)) = k1_relat_1(k5_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,(
    ! [A_76,A_13] :
      ( k1_relat_1(k5_relat_1(A_76,k6_relat_1(A_13))) = k10_relat_1(A_76,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_245])).

tff(c_271,plain,(
    ! [A_78,A_79] :
      ( k1_relat_1(k5_relat_1(A_78,k6_relat_1(A_79))) = k10_relat_1(A_78,A_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_262])).

tff(c_458,plain,(
    ! [B_94,A_95] :
      ( k10_relat_1(B_94,A_95) = k1_relat_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v5_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_271])).

tff(c_464,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_458])).

tff(c_470,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_464])).

tff(c_403,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k8_relset_1(A_88,B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_406,plain,(
    ! [D_91] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_91) = k10_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_40,c_403])).

tff(c_336,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_339,plain,(
    ! [D_85] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_85) = k9_relat_1('#skF_3',D_85) ),
    inference(resolution,[status(thm)],[c_40,c_336])).

tff(c_235,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_239,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_235])).

tff(c_38,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_102,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_240,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_102])).

tff(c_340,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_240])).

tff(c_448,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_340])).

tff(c_477,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_448])).

tff(c_484,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_477])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_484])).

tff(c_489,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_601,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_489])).

tff(c_912,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_601])).

tff(c_963,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_930,c_912])).

tff(c_966,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_963])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/2.12  
% 3.45/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/2.14  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.45/2.14  
% 3.45/2.14  %Foreground sorts:
% 3.45/2.14  
% 3.45/2.14  
% 3.45/2.14  %Background operators:
% 3.45/2.14  
% 3.45/2.14  
% 3.45/2.14  %Foreground operators:
% 3.45/2.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.45/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/2.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.45/2.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.45/2.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.45/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/2.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.45/2.14  tff('#skF_2', type, '#skF_2': $i).
% 3.45/2.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.45/2.14  tff('#skF_3', type, '#skF_3': $i).
% 3.45/2.14  tff('#skF_1', type, '#skF_1': $i).
% 3.45/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.45/2.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.45/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/2.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.45/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/2.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.45/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/2.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.45/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/2.14  
% 3.57/2.18  tff(f_101, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.57/2.18  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.57/2.18  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.57/2.18  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/2.18  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.57/2.18  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.57/2.18  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.57/2.18  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.57/2.18  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.57/2.18  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.57/2.18  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.57/2.18  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.57/2.18  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.57/2.18  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.57/2.18  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.57/2.18  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.57/2.18  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.57/2.18  tff(c_74, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/2.18  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_74])).
% 3.57/2.18  tff(c_12, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/2.18  tff(c_544, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/2.18  tff(c_548, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_544])).
% 3.57/2.18  tff(c_554, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=B_116 | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/2.18  tff(c_557, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_548, c_554])).
% 3.57/2.18  tff(c_560, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_557])).
% 3.57/2.18  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/2.18  tff(c_564, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_560, c_10])).
% 3.57/2.18  tff(c_568, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_564])).
% 3.57/2.18  tff(c_927, plain, (![A_147, B_148, C_149, D_150]: (k7_relset_1(A_147, B_148, C_149, D_150)=k9_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.57/2.18  tff(c_930, plain, (![D_150]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_150)=k9_relat_1('#skF_3', D_150))), inference(resolution, [status(thm)], [c_40, c_927])).
% 3.57/2.18  tff(c_907, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.57/2.18  tff(c_910, plain, (![D_145]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_145)=k10_relat_1('#skF_3', D_145))), inference(resolution, [status(thm)], [c_40, c_907])).
% 3.57/2.18  tff(c_596, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.57/2.18  tff(c_600, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_596])).
% 3.57/2.18  tff(c_8, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/2.18  tff(c_124, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/2.18  tff(c_128, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_124])).
% 3.57/2.18  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/2.18  tff(c_182, plain, (![B_64, A_65]: (k5_relat_1(B_64, k6_relat_1(A_65))=B_64 | ~r1_tarski(k2_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.57/2.18  tff(c_192, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_182])).
% 3.57/2.18  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.57/2.18  tff(c_18, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/2.18  tff(c_245, plain, (![A_76, B_77]: (k10_relat_1(A_76, k1_relat_1(B_77))=k1_relat_1(k5_relat_1(A_76, B_77)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/2.18  tff(c_262, plain, (![A_76, A_13]: (k1_relat_1(k5_relat_1(A_76, k6_relat_1(A_13)))=k10_relat_1(A_76, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_245])).
% 3.57/2.18  tff(c_271, plain, (![A_78, A_79]: (k1_relat_1(k5_relat_1(A_78, k6_relat_1(A_79)))=k10_relat_1(A_78, A_79) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_262])).
% 3.57/2.18  tff(c_458, plain, (![B_94, A_95]: (k10_relat_1(B_94, A_95)=k1_relat_1(B_94) | ~v1_relat_1(B_94) | ~v5_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(superposition, [status(thm), theory('equality')], [c_192, c_271])).
% 3.57/2.18  tff(c_464, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_458])).
% 3.57/2.18  tff(c_470, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_464])).
% 3.57/2.18  tff(c_403, plain, (![A_88, B_89, C_90, D_91]: (k8_relset_1(A_88, B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.57/2.18  tff(c_406, plain, (![D_91]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_91)=k10_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_40, c_403])).
% 3.57/2.18  tff(c_336, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.57/2.18  tff(c_339, plain, (![D_85]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_85)=k9_relat_1('#skF_3', D_85))), inference(resolution, [status(thm)], [c_40, c_336])).
% 3.57/2.18  tff(c_235, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.57/2.18  tff(c_239, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_235])).
% 3.57/2.18  tff(c_38, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.57/2.18  tff(c_102, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.57/2.18  tff(c_240, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_102])).
% 3.57/2.18  tff(c_340, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_240])).
% 3.57/2.18  tff(c_448, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_340])).
% 3.57/2.18  tff(c_477, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_448])).
% 3.57/2.18  tff(c_484, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_477])).
% 3.57/2.18  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_484])).
% 3.57/2.18  tff(c_489, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.57/2.18  tff(c_601, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_600, c_489])).
% 3.57/2.18  tff(c_912, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_601])).
% 3.57/2.18  tff(c_963, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_568, c_930, c_912])).
% 3.57/2.18  tff(c_966, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_963])).
% 3.57/2.18  tff(c_970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_966])).
% 3.57/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/2.18  
% 3.57/2.18  Inference rules
% 3.57/2.18  ----------------------
% 3.57/2.18  #Ref     : 0
% 3.57/2.18  #Sup     : 209
% 3.57/2.18  #Fact    : 0
% 3.57/2.18  #Define  : 0
% 3.57/2.18  #Split   : 1
% 3.57/2.18  #Chain   : 0
% 3.57/2.18  #Close   : 0
% 3.57/2.18  
% 3.57/2.18  Ordering : KBO
% 3.57/2.18  
% 3.57/2.18  Simplification rules
% 3.57/2.18  ----------------------
% 3.57/2.18  #Subsume      : 7
% 3.57/2.18  #Demod        : 144
% 3.57/2.18  #Tautology    : 125
% 3.57/2.18  #SimpNegUnit  : 0
% 3.57/2.18  #BackRed      : 8
% 3.57/2.18  
% 3.57/2.18  #Partial instantiations: 0
% 3.57/2.18  #Strategies tried      : 1
% 3.57/2.18  
% 3.57/2.18  Timing (in seconds)
% 3.57/2.18  ----------------------
% 3.57/2.18  Preprocessing        : 0.56
% 3.57/2.18  Parsing              : 0.32
% 3.57/2.18  CNF conversion       : 0.03
% 3.57/2.18  Main loop            : 0.64
% 3.57/2.18  Inferencing          : 0.28
% 3.57/2.18  Reduction            : 0.20
% 3.57/2.19  Demodulation         : 0.13
% 3.57/2.19  BG Simplification    : 0.04
% 3.57/2.19  Subsumption          : 0.08
% 3.57/2.19  Abstraction          : 0.04
% 3.57/2.19  MUC search           : 0.00
% 3.57/2.19  Cooper               : 0.00
% 3.57/2.19  Total                : 1.28
% 3.57/2.19  Index Insertion      : 0.00
% 3.57/2.19  Index Deletion       : 0.00
% 3.57/2.19  Index Matching       : 0.00
% 3.57/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
