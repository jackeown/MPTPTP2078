%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 105 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 155 expanded)
%              Number of equality atoms :   43 (  65 expanded)
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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_445,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k8_relset_1(A_114,B_115,C_116,D_117) = k10_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_448,plain,(
    ! [D_117] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_117) = k10_relat_1('#skF_3',D_117) ),
    inference(resolution,[status(thm)],[c_36,c_445])).

tff(c_415,plain,(
    ! [A_109,B_110,C_111] :
      ( k1_relset_1(A_109,B_110,C_111) = k1_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_419,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_415])).

tff(c_56,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_87,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_12])).

tff(c_97,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_94])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_118,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_114])).

tff(c_277,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k7_relset_1(A_83,B_84,C_85,D_86) = k9_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_280,plain,(
    ! [D_86] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_86) = k9_relat_1('#skF_3',D_86) ),
    inference(resolution,[status(thm)],[c_36,c_277])).

tff(c_173,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_177,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_34,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_178,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_76])).

tff(c_281,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_178])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_281])).

tff(c_285,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_420,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_285])).

tff(c_449,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_420])).

tff(c_71,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [B_98,A_99] :
      ( k5_relat_1(B_98,k6_relat_1(A_99)) = B_98
      | ~ r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_334,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_324])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_401,plain,(
    ! [A_107,B_108] :
      ( k10_relat_1(A_107,k1_relat_1(B_108)) = k1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_410,plain,(
    ! [A_107,A_11] :
      ( k1_relat_1(k5_relat_1(A_107,k6_relat_1(A_11))) = k10_relat_1(A_107,A_11)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_401])).

tff(c_425,plain,(
    ! [A_112,A_113] :
      ( k1_relat_1(k5_relat_1(A_112,k6_relat_1(A_113))) = k10_relat_1(A_112,A_113)
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_410])).

tff(c_480,plain,(
    ! [B_121,A_122] :
      ( k10_relat_1(B_121,A_122) = k1_relat_1(B_121)
      | ~ v1_relat_1(B_121)
      | ~ v5_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_425])).

tff(c_486,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_480])).

tff(c_492,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_486])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.41  
% 2.18/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.41  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.41  
% 2.18/1.41  %Foreground sorts:
% 2.18/1.41  
% 2.18/1.41  
% 2.18/1.41  %Background operators:
% 2.18/1.41  
% 2.18/1.41  
% 2.18/1.41  %Foreground operators:
% 2.18/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.18/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.18/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.18/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.18/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.18/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.41  
% 2.18/1.43  tff(f_93, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.18/1.43  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.18/1.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.43  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.18/1.43  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.18/1.43  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.18/1.43  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.18/1.43  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.18/1.43  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.18/1.43  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.18/1.43  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.18/1.43  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.18/1.43  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.18/1.43  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.18/1.43  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.18/1.43  tff(c_445, plain, (![A_114, B_115, C_116, D_117]: (k8_relset_1(A_114, B_115, C_116, D_117)=k10_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.18/1.43  tff(c_448, plain, (![D_117]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_117)=k10_relat_1('#skF_3', D_117))), inference(resolution, [status(thm)], [c_36, c_445])).
% 2.18/1.43  tff(c_415, plain, (![A_109, B_110, C_111]: (k1_relset_1(A_109, B_110, C_111)=k1_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.43  tff(c_419, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_415])).
% 2.18/1.43  tff(c_56, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.43  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.18/1.43  tff(c_87, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.43  tff(c_91, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_87])).
% 2.18/1.43  tff(c_12, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.43  tff(c_94, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_91, c_12])).
% 2.18/1.43  tff(c_97, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_94])).
% 2.18/1.43  tff(c_8, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.43  tff(c_114, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 2.18/1.43  tff(c_118, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_114])).
% 2.18/1.43  tff(c_277, plain, (![A_83, B_84, C_85, D_86]: (k7_relset_1(A_83, B_84, C_85, D_86)=k9_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.43  tff(c_280, plain, (![D_86]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_86)=k9_relat_1('#skF_3', D_86))), inference(resolution, [status(thm)], [c_36, c_277])).
% 2.18/1.43  tff(c_173, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.18/1.43  tff(c_177, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_173])).
% 2.18/1.43  tff(c_34, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.18/1.43  tff(c_76, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.18/1.43  tff(c_178, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_76])).
% 2.18/1.43  tff(c_281, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_178])).
% 2.18/1.43  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_281])).
% 2.18/1.43  tff(c_285, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.18/1.43  tff(c_420, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_285])).
% 2.18/1.43  tff(c_449, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_420])).
% 2.18/1.43  tff(c_71, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.43  tff(c_75, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.18/1.43  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.43  tff(c_324, plain, (![B_98, A_99]: (k5_relat_1(B_98, k6_relat_1(A_99))=B_98 | ~r1_tarski(k2_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.43  tff(c_334, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_324])).
% 2.18/1.43  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.43  tff(c_14, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.43  tff(c_401, plain, (![A_107, B_108]: (k10_relat_1(A_107, k1_relat_1(B_108))=k1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.43  tff(c_410, plain, (![A_107, A_11]: (k1_relat_1(k5_relat_1(A_107, k6_relat_1(A_11)))=k10_relat_1(A_107, A_11) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_14, c_401])).
% 2.18/1.43  tff(c_425, plain, (![A_112, A_113]: (k1_relat_1(k5_relat_1(A_112, k6_relat_1(A_113)))=k10_relat_1(A_112, A_113) | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_410])).
% 2.18/1.43  tff(c_480, plain, (![B_121, A_122]: (k10_relat_1(B_121, A_122)=k1_relat_1(B_121) | ~v1_relat_1(B_121) | ~v5_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(superposition, [status(thm), theory('equality')], [c_334, c_425])).
% 2.18/1.43  tff(c_486, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_480])).
% 2.18/1.43  tff(c_492, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_486])).
% 2.18/1.43  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_492])).
% 2.18/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.43  
% 2.18/1.43  Inference rules
% 2.18/1.43  ----------------------
% 2.18/1.43  #Ref     : 0
% 2.18/1.43  #Sup     : 105
% 2.18/1.43  #Fact    : 0
% 2.18/1.43  #Define  : 0
% 2.18/1.43  #Split   : 1
% 2.18/1.43  #Chain   : 0
% 2.18/1.43  #Close   : 0
% 2.18/1.43  
% 2.18/1.43  Ordering : KBO
% 2.18/1.43  
% 2.18/1.43  Simplification rules
% 2.18/1.43  ----------------------
% 2.18/1.43  #Subsume      : 2
% 2.18/1.43  #Demod        : 36
% 2.18/1.43  #Tautology    : 60
% 2.18/1.43  #SimpNegUnit  : 1
% 2.18/1.43  #BackRed      : 5
% 2.18/1.43  
% 2.18/1.43  #Partial instantiations: 0
% 2.18/1.43  #Strategies tried      : 1
% 2.18/1.43  
% 2.18/1.43  Timing (in seconds)
% 2.18/1.43  ----------------------
% 2.18/1.43  Preprocessing        : 0.31
% 2.18/1.43  Parsing              : 0.16
% 2.18/1.43  CNF conversion       : 0.02
% 2.18/1.43  Main loop            : 0.25
% 2.18/1.43  Inferencing          : 0.10
% 2.18/1.43  Reduction            : 0.07
% 2.18/1.43  Demodulation         : 0.05
% 2.18/1.43  BG Simplification    : 0.02
% 2.18/1.43  Subsumption          : 0.03
% 2.18/1.43  Abstraction          : 0.01
% 2.18/1.43  MUC search           : 0.00
% 2.18/1.43  Cooper               : 0.00
% 2.18/1.43  Total                : 0.59
% 2.18/1.43  Index Insertion      : 0.00
% 2.18/1.43  Index Deletion       : 0.00
% 2.18/1.43  Index Matching       : 0.00
% 2.18/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
