%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 10.79s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 216 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 385 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_65,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_71])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_642,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ r1_tarski(k2_relat_1(C_112),B_114)
      | ~ r1_tarski(k1_relat_1(C_112),A_113)
      | ~ v1_relat_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_520,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k5_relset_1(A_99,B_100,C_101,D_102) = k7_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_527,plain,(
    ! [D_102] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_102) = k7_relat_1('#skF_4',D_102) ),
    inference(resolution,[status(thm)],[c_40,c_520])).

tff(c_38,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_529,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_38])).

tff(c_660,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_642,c_529])).

tff(c_685,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_691,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_685])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_691])).

tff(c_698,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_249,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_81,A_82)),k1_relat_1(B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_135,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_152,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_155,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_152])).

tff(c_158,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_155])).

tff(c_162,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_24])).

tff(c_169,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_162])).

tff(c_183,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,'#skF_1')
      | ~ r1_tarski(A_71,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_169,c_183])).

tff(c_253,plain,(
    ! [A_82] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_82)),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_249,c_192])).

tff(c_267,plain,(
    ! [A_82] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_82)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_253])).

tff(c_28,plain,(
    ! [A_27] :
      ( k7_relat_1(A_27,k1_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_369,plain,(
    ! [C_90,B_91,A_92] :
      ( k7_relat_1(k7_relat_1(C_90,B_91),A_92) = k7_relat_1(C_90,A_92)
      | ~ r1_tarski(A_92,B_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3379,plain,(
    ! [C_297,B_298] :
      ( k7_relat_1(C_297,k1_relat_1(k7_relat_1(C_297,B_298))) = k7_relat_1(C_297,B_298)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_297,B_298)),B_298)
      | ~ v1_relat_1(C_297)
      | ~ v1_relat_1(k7_relat_1(C_297,B_298)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_369])).

tff(c_13884,plain,(
    ! [B_676,A_677] :
      ( k7_relat_1(B_676,k1_relat_1(k7_relat_1(B_676,A_677))) = k7_relat_1(B_676,A_677)
      | ~ v1_relat_1(k7_relat_1(B_676,A_677))
      | ~ v1_relat_1(B_676) ) ),
    inference(resolution,[status(thm)],[c_24,c_3379])).

tff(c_272,plain,(
    ! [C_83,A_84,B_85] :
      ( r1_tarski(k7_relat_1(C_83,A_84),k7_relat_1(C_83,B_85))
      | ~ r1_tarski(A_84,B_85)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_283,plain,(
    ! [A_84] :
      ( r1_tarski(k7_relat_1('#skF_4',A_84),'#skF_4')
      | ~ r1_tarski(A_84,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_272])).

tff(c_295,plain,(
    ! [A_84] :
      ( r1_tarski(k7_relat_1('#skF_4',A_84),'#skF_4')
      | ~ r1_tarski(A_84,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_283])).

tff(c_14292,plain,(
    ! [A_677] :
      ( r1_tarski(k7_relat_1('#skF_4',A_677),'#skF_4')
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_677)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_677))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13884,c_295])).

tff(c_14495,plain,(
    ! [A_678] :
      ( r1_tarski(k7_relat_1('#skF_4',A_678),'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_678)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_267,c_14292])).

tff(c_44,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_207,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_183])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_103,plain,(
    ! [A_4,B_54,A_55] :
      ( v5_relat_1(A_4,B_54)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_55,B_54)) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_226,plain,(
    ! [A_75] :
      ( v5_relat_1(A_75,'#skF_3')
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_207,c_103])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_697,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_805,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_697])).

tff(c_808,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_805])).

tff(c_811,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_808])).

tff(c_819,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_811])).

tff(c_14511,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14495,c_819])).

tff(c_14555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_14511])).

tff(c_14556,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_697])).

tff(c_14560,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_14556])).

tff(c_14564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_14560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.79/4.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/4.36  
% 10.79/4.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/4.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.79/4.37  
% 10.79/4.37  %Foreground sorts:
% 10.79/4.37  
% 10.79/4.37  
% 10.79/4.37  %Background operators:
% 10.79/4.37  
% 10.79/4.37  
% 10.79/4.37  %Foreground operators:
% 10.79/4.37  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 10.79/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.79/4.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.79/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.79/4.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.79/4.37  tff('#skF_2', type, '#skF_2': $i).
% 10.79/4.37  tff('#skF_3', type, '#skF_3': $i).
% 10.79/4.37  tff('#skF_1', type, '#skF_1': $i).
% 10.79/4.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.79/4.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.79/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.79/4.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.79/4.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.79/4.37  tff('#skF_4', type, '#skF_4': $i).
% 10.79/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.79/4.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.79/4.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.79/4.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.79/4.37  
% 10.93/4.38  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.93/4.38  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 10.93/4.38  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.93/4.38  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 10.93/4.38  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 10.93/4.38  tff(f_102, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 10.93/4.38  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 10.93/4.38  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 10.93/4.38  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.93/4.38  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 10.93/4.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.93/4.38  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 10.93/4.38  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 10.93/4.38  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_relat_1)).
% 10.93/4.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.93/4.38  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.93/4.38  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.93/4.38  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.38  tff(c_65, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.93/4.38  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_65])).
% 10.93/4.38  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_71])).
% 10.93/4.38  tff(c_24, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.93/4.38  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.93/4.38  tff(c_642, plain, (![C_112, A_113, B_114]: (m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~r1_tarski(k2_relat_1(C_112), B_114) | ~r1_tarski(k1_relat_1(C_112), A_113) | ~v1_relat_1(C_112))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.93/4.38  tff(c_520, plain, (![A_99, B_100, C_101, D_102]: (k5_relset_1(A_99, B_100, C_101, D_102)=k7_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.93/4.38  tff(c_527, plain, (![D_102]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_102)=k7_relat_1('#skF_4', D_102))), inference(resolution, [status(thm)], [c_40, c_520])).
% 10.93/4.38  tff(c_38, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.38  tff(c_529, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_38])).
% 10.93/4.38  tff(c_660, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_642, c_529])).
% 10.93/4.38  tff(c_685, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_660])).
% 10.93/4.38  tff(c_691, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_685])).
% 10.93/4.38  tff(c_696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_691])).
% 10.93/4.38  tff(c_698, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_660])).
% 10.93/4.38  tff(c_249, plain, (![B_81, A_82]: (r1_tarski(k1_relat_1(k7_relat_1(B_81, A_82)), k1_relat_1(B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.93/4.38  tff(c_126, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.93/4.38  tff(c_135, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_126])).
% 10.93/4.38  tff(c_152, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.93/4.38  tff(c_155, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_152])).
% 10.93/4.38  tff(c_158, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_155])).
% 10.93/4.38  tff(c_162, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_24])).
% 10.93/4.38  tff(c_169, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_162])).
% 10.93/4.38  tff(c_183, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.93/4.38  tff(c_192, plain, (![A_71]: (r1_tarski(A_71, '#skF_1') | ~r1_tarski(A_71, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_169, c_183])).
% 10.93/4.38  tff(c_253, plain, (![A_82]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_82)), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_249, c_192])).
% 10.93/4.38  tff(c_267, plain, (![A_82]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_82)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_253])).
% 10.93/4.38  tff(c_28, plain, (![A_27]: (k7_relat_1(A_27, k1_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.93/4.38  tff(c_369, plain, (![C_90, B_91, A_92]: (k7_relat_1(k7_relat_1(C_90, B_91), A_92)=k7_relat_1(C_90, A_92) | ~r1_tarski(A_92, B_91) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.93/4.38  tff(c_3379, plain, (![C_297, B_298]: (k7_relat_1(C_297, k1_relat_1(k7_relat_1(C_297, B_298)))=k7_relat_1(C_297, B_298) | ~r1_tarski(k1_relat_1(k7_relat_1(C_297, B_298)), B_298) | ~v1_relat_1(C_297) | ~v1_relat_1(k7_relat_1(C_297, B_298)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_369])).
% 10.93/4.38  tff(c_13884, plain, (![B_676, A_677]: (k7_relat_1(B_676, k1_relat_1(k7_relat_1(B_676, A_677)))=k7_relat_1(B_676, A_677) | ~v1_relat_1(k7_relat_1(B_676, A_677)) | ~v1_relat_1(B_676))), inference(resolution, [status(thm)], [c_24, c_3379])).
% 10.93/4.38  tff(c_272, plain, (![C_83, A_84, B_85]: (r1_tarski(k7_relat_1(C_83, A_84), k7_relat_1(C_83, B_85)) | ~r1_tarski(A_84, B_85) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.93/4.38  tff(c_283, plain, (![A_84]: (r1_tarski(k7_relat_1('#skF_4', A_84), '#skF_4') | ~r1_tarski(A_84, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_272])).
% 10.93/4.38  tff(c_295, plain, (![A_84]: (r1_tarski(k7_relat_1('#skF_4', A_84), '#skF_4') | ~r1_tarski(A_84, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_283])).
% 10.93/4.38  tff(c_14292, plain, (![A_677]: (r1_tarski(k7_relat_1('#skF_4', A_677), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_677)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', A_677)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13884, c_295])).
% 10.93/4.38  tff(c_14495, plain, (![A_678]: (r1_tarski(k7_relat_1('#skF_4', A_678), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', A_678)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_267, c_14292])).
% 10.93/4.38  tff(c_44, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.93/4.38  tff(c_52, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_44])).
% 10.93/4.38  tff(c_207, plain, (![A_75]: (r1_tarski(A_75, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_183])).
% 10.93/4.38  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.93/4.38  tff(c_95, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.93/4.38  tff(c_103, plain, (![A_4, B_54, A_55]: (v5_relat_1(A_4, B_54) | ~r1_tarski(A_4, k2_zfmisc_1(A_55, B_54)))), inference(resolution, [status(thm)], [c_6, c_95])).
% 10.93/4.38  tff(c_226, plain, (![A_75]: (v5_relat_1(A_75, '#skF_3') | ~r1_tarski(A_75, '#skF_4'))), inference(resolution, [status(thm)], [c_207, c_103])).
% 10.93/4.38  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.93/4.38  tff(c_697, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_660])).
% 10.93/4.38  tff(c_805, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_697])).
% 10.93/4.38  tff(c_808, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_805])).
% 10.93/4.38  tff(c_811, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_698, c_808])).
% 10.93/4.38  tff(c_819, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_226, c_811])).
% 10.93/4.38  tff(c_14511, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_14495, c_819])).
% 10.93/4.38  tff(c_14555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_698, c_14511])).
% 10.93/4.38  tff(c_14556, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_697])).
% 10.93/4.38  tff(c_14560, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_14556])).
% 10.93/4.38  tff(c_14564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_14560])).
% 10.93/4.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.38  
% 10.93/4.38  Inference rules
% 10.93/4.38  ----------------------
% 10.93/4.38  #Ref     : 0
% 10.93/4.38  #Sup     : 3211
% 10.93/4.38  #Fact    : 0
% 10.93/4.38  #Define  : 0
% 10.93/4.38  #Split   : 15
% 10.93/4.38  #Chain   : 0
% 10.93/4.38  #Close   : 0
% 10.93/4.38  
% 10.93/4.38  Ordering : KBO
% 10.93/4.38  
% 10.93/4.38  Simplification rules
% 10.93/4.38  ----------------------
% 10.93/4.38  #Subsume      : 597
% 10.93/4.38  #Demod        : 1938
% 10.93/4.38  #Tautology    : 641
% 10.93/4.38  #SimpNegUnit  : 11
% 10.93/4.38  #BackRed      : 6
% 10.93/4.38  
% 10.93/4.38  #Partial instantiations: 0
% 10.93/4.38  #Strategies tried      : 1
% 10.93/4.38  
% 10.93/4.38  Timing (in seconds)
% 10.93/4.38  ----------------------
% 10.93/4.39  Preprocessing        : 0.33
% 10.93/4.39  Parsing              : 0.18
% 10.93/4.39  CNF conversion       : 0.02
% 10.93/4.39  Main loop            : 3.32
% 10.93/4.39  Inferencing          : 0.77
% 10.93/4.39  Reduction            : 1.27
% 10.93/4.39  Demodulation         : 0.99
% 10.93/4.39  BG Simplification    : 0.08
% 10.93/4.39  Subsumption          : 0.97
% 10.93/4.39  Abstraction          : 0.11
% 10.93/4.39  MUC search           : 0.00
% 10.93/4.39  Cooper               : 0.00
% 10.93/4.39  Total                : 3.68
% 10.93/4.39  Index Insertion      : 0.00
% 10.93/4.39  Index Deletion       : 0.00
% 10.93/4.39  Index Matching       : 0.00
% 10.93/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
