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
% DateTime   : Thu Dec  3 10:07:58 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 137 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 207 expanded)
%              Number of equality atoms :   52 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_14,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_354,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k8_relset_1(A_102,B_103,C_104,D_105) = k10_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_357,plain,(
    ! [D_105] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_105) = k10_relat_1('#skF_3',D_105) ),
    inference(resolution,[status(thm)],[c_34,c_354])).

tff(c_59,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_64,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ v4_relat_1(B_43,A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_64])).

tff(c_70,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_67])).

tff(c_257,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k7_relat_1(B_79,A_80)) = k9_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_269,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_257])).

tff(c_273,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_269])).

tff(c_350,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_353,plain,(
    ! [D_101] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_101) = k9_relat_1('#skF_3',D_101) ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_326,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_330,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_326])).

tff(c_8,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_106,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    ! [B_56,A_57] :
      ( k3_xboole_0(k2_relat_1(B_56),A_57) = k2_relat_1(B_56)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(B_9,k3_xboole_0(k2_relat_1(B_9),A_8)) = k10_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_192,plain,(
    ! [B_74,A_75] :
      ( k10_relat_1(B_74,k2_relat_1(B_74)) = k10_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_12])).

tff(c_194,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_192])).

tff(c_197,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_194])).

tff(c_201,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_14])).

tff(c_208,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201])).

tff(c_178,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_181,plain,(
    ! [D_72] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_72) = k10_relat_1('#skF_3',D_72) ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_164,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k7_relset_1(A_64,B_65,C_66,D_67) = k9_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_167,plain,(
    ! [D_67] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_67) = k9_relat_1('#skF_3',D_67) ),
    inference(resolution,[status(thm)],[c_34,c_164])).

tff(c_145,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_149,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_145])).

tff(c_32,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_150,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_71])).

tff(c_168,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_150])).

tff(c_182,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_168])).

tff(c_213,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_182])).

tff(c_246,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_213])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_246])).

tff(c_251,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_331,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_251])).

tff(c_358,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_331])).

tff(c_359,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_358])).

tff(c_385,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_359])).

tff(c_388,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_385])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.29  
% 2.18/1.29  %Foreground sorts:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Background operators:
% 2.18/1.29  
% 2.18/1.29  
% 2.18/1.29  %Foreground operators:
% 2.18/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.18/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.29  
% 2.18/1.31  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.18/1.31  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.31  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.18/1.31  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.18/1.31  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.18/1.31  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.18/1.31  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.18/1.31  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.18/1.31  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.31  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.18/1.31  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.18/1.31  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.18/1.31  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.18/1.31  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.18/1.31  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.31  tff(c_36, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.31  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.18/1.31  tff(c_14, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.31  tff(c_354, plain, (![A_102, B_103, C_104, D_105]: (k8_relset_1(A_102, B_103, C_104, D_105)=k10_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.31  tff(c_357, plain, (![D_105]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_105)=k10_relat_1('#skF_3', D_105))), inference(resolution, [status(thm)], [c_34, c_354])).
% 2.18/1.31  tff(c_59, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.31  tff(c_63, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.18/1.31  tff(c_64, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~v4_relat_1(B_43, A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.31  tff(c_67, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_63, c_64])).
% 2.18/1.31  tff(c_70, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_67])).
% 2.18/1.31  tff(c_257, plain, (![B_79, A_80]: (k2_relat_1(k7_relat_1(B_79, A_80))=k9_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.31  tff(c_269, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70, c_257])).
% 2.18/1.31  tff(c_273, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_269])).
% 2.18/1.31  tff(c_350, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_353, plain, (![D_101]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_101)=k9_relat_1('#skF_3', D_101))), inference(resolution, [status(thm)], [c_34, c_350])).
% 2.18/1.31  tff(c_326, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.31  tff(c_330, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_326])).
% 2.18/1.31  tff(c_8, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.31  tff(c_101, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.31  tff(c_105, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_101])).
% 2.18/1.31  tff(c_106, plain, (![B_52, A_53]: (r1_tarski(k2_relat_1(B_52), A_53) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.31  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.31  tff(c_130, plain, (![B_56, A_57]: (k3_xboole_0(k2_relat_1(B_56), A_57)=k2_relat_1(B_56) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.18/1.31  tff(c_12, plain, (![B_9, A_8]: (k10_relat_1(B_9, k3_xboole_0(k2_relat_1(B_9), A_8))=k10_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.31  tff(c_192, plain, (![B_74, A_75]: (k10_relat_1(B_74, k2_relat_1(B_74))=k10_relat_1(B_74, A_75) | ~v1_relat_1(B_74) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_130, c_12])).
% 2.18/1.31  tff(c_194, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_192])).
% 2.18/1.31  tff(c_197, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_194])).
% 2.18/1.31  tff(c_201, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_197, c_14])).
% 2.18/1.31  tff(c_208, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201])).
% 2.18/1.31  tff(c_178, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.31  tff(c_181, plain, (![D_72]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_72)=k10_relat_1('#skF_3', D_72))), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.18/1.31  tff(c_164, plain, (![A_64, B_65, C_66, D_67]: (k7_relset_1(A_64, B_65, C_66, D_67)=k9_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_167, plain, (![D_67]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_67)=k9_relat_1('#skF_3', D_67))), inference(resolution, [status(thm)], [c_34, c_164])).
% 2.18/1.31  tff(c_145, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.31  tff(c_149, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_145])).
% 2.18/1.31  tff(c_32, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.31  tff(c_71, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.18/1.31  tff(c_150, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_71])).
% 2.18/1.31  tff(c_168, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_150])).
% 2.18/1.31  tff(c_182, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_168])).
% 2.18/1.31  tff(c_213, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_182])).
% 2.18/1.31  tff(c_246, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_213])).
% 2.18/1.31  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_246])).
% 2.18/1.31  tff(c_251, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.18/1.31  tff(c_331, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_251])).
% 2.18/1.31  tff(c_358, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_331])).
% 2.18/1.31  tff(c_359, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_358])).
% 2.18/1.31  tff(c_385, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_359])).
% 2.18/1.31  tff(c_388, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_385])).
% 2.18/1.31  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_388])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 90
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 1
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 0
% 2.18/1.31  #Demod        : 26
% 2.18/1.31  #Tautology    : 53
% 2.18/1.31  #SimpNegUnit  : 0
% 2.18/1.31  #BackRed      : 8
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.31  Preprocessing        : 0.31
% 2.18/1.31  Parsing              : 0.17
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.23
% 2.18/1.31  Inferencing          : 0.10
% 2.18/1.31  Reduction            : 0.06
% 2.18/1.31  Demodulation         : 0.05
% 2.18/1.31  BG Simplification    : 0.02
% 2.18/1.31  Subsumption          : 0.03
% 2.18/1.31  Abstraction          : 0.02
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.59
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
