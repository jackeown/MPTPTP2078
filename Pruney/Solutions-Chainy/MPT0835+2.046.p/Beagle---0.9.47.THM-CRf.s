%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:02 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 277 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 468 expanded)
%              Number of equality atoms :   69 ( 182 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k6_relset_1 > k5_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2864,plain,(
    ! [A_283,B_284,C_285,D_286] :
      ( k7_relset_1(A_283,B_284,C_285,D_286) = k9_relat_1(C_285,D_286)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2867,plain,(
    ! [D_286] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_286) = k9_relat_1('#skF_3',D_286) ),
    inference(resolution,[status(thm)],[c_38,c_2864])).

tff(c_2840,plain,(
    ! [A_277,B_278,C_279] :
      ( k2_relset_1(A_277,B_278,C_279) = k2_relat_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2844,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2840])).

tff(c_2947,plain,(
    ! [A_303,B_304,C_305] :
      ( k7_relset_1(A_303,B_304,C_305,A_303) = k2_relset_1(A_303,B_304,C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2949,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2947])).

tff(c_2951,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2867,c_2844,c_2949])).

tff(c_2902,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k8_relset_1(A_293,B_294,C_295,D_296) = k10_relat_1(C_295,D_296)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2905,plain,(
    ! [D_296] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_296) = k10_relat_1('#skF_3',D_296) ),
    inference(resolution,[status(thm)],[c_38,c_2902])).

tff(c_2849,plain,(
    ! [A_280,B_281,C_282] :
      ( k1_relset_1(A_280,B_281,C_282) = k1_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2853,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2849])).

tff(c_132,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k8_relset_1(A_74,B_75,C_76,D_77) = k10_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_135,plain,(
    ! [D_77] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_77) = k10_relat_1('#skF_3',D_77) ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_96,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_169,plain,(
    ! [A_87,B_88,C_89] :
      ( k8_relset_1(A_87,B_88,C_89,B_88) = k1_relset_1(A_87,B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_173,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_100,c_171])).

tff(c_146,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    ! [D_82] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_82) = k9_relat_1('#skF_3',D_82) ),
    inference(resolution,[status(thm)],[c_38,c_146])).

tff(c_87,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_36,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_77,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_105,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_77])).

tff(c_136,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_105])).

tff(c_150,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_136])).

tff(c_174,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_150])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(k1_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [B_52] :
      ( k7_relat_1(B_52,k1_relat_1(B_52)) = B_52
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_106,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k5_relset_1(A_64,B_65,C_66,D_67) = k7_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [D_67] : k5_relset_1('#skF_2','#skF_1','#skF_3',D_67) = k7_relat_1('#skF_3',D_67) ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_295,plain,(
    ! [A_96,C_97,D_98,B_99] :
      ( m1_subset_1(k5_relset_1(A_96,C_97,D_98,B_99),k1_zfmisc_1(k2_zfmisc_1(B_99,C_97)))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_96,C_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_319,plain,(
    ! [D_67] :
      ( m1_subset_1(k7_relat_1('#skF_3',D_67),k1_zfmisc_1(k2_zfmisc_1(D_67,'#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_295])).

tff(c_341,plain,(
    ! [D_100] : m1_subset_1(k7_relat_1('#skF_3',D_100),k1_zfmisc_1(k2_zfmisc_1(D_100,'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_319])).

tff(c_366,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_341])).

tff(c_379,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_366])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( k7_relset_1(A_26,B_27,C_28,D_29) = k9_relat_1(C_28,D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_425,plain,(
    ! [D_29] : k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',D_29) = k9_relat_1('#skF_3',D_29) ),
    inference(resolution,[status(thm)],[c_379,c_24])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_430,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_379,c_18])).

tff(c_34,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_relset_1(A_42,B_43,C_44,A_42) = k2_relset_1(A_42,B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_424,plain,(
    k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',k1_relat_1('#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_379,c_34])).

tff(c_2827,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_430,c_424])).

tff(c_2828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_2827])).

tff(c_2829,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2863,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_2829])).

tff(c_2868,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2867,c_2863])).

tff(c_2907,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2905,c_2868])).

tff(c_2952,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2951,c_2907])).

tff(c_71,plain,(
    ! [A_55,B_56] :
      ( k8_relat_1(A_55,B_56) = B_56
      | ~ r1_tarski(k2_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [B_56] :
      ( k8_relat_1(k2_relat_1(B_56),B_56) = B_56
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_2888,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( k6_relset_1(A_288,B_289,C_290,D_291) = k8_relat_1(C_290,D_291)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2891,plain,(
    ! [C_290] : k6_relset_1('#skF_2','#skF_1',C_290,'#skF_3') = k8_relat_1(C_290,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_2888])).

tff(c_2984,plain,(
    ! [C_309,A_310,B_311,D_312] :
      ( m1_subset_1(k6_relset_1(C_309,A_310,B_311,D_312),k1_zfmisc_1(k2_zfmisc_1(C_309,B_311)))
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(C_309,A_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3008,plain,(
    ! [C_290] :
      ( m1_subset_1(k8_relat_1(C_290,'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',C_290)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2891,c_2984])).

tff(c_3022,plain,(
    ! [C_313] : m1_subset_1(k8_relat_1(C_313,'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',C_313))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3008])).

tff(c_3047,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_3'))))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_3022])).

tff(c_3060,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3047])).

tff(c_26,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k8_relset_1(A_30,B_31,C_32,D_33) = k10_relat_1(C_32,D_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3130,plain,(
    ! [D_33] : k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',D_33) = k10_relat_1('#skF_3',D_33) ),
    inference(resolution,[status(thm)],[c_3060,c_26])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3133,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3060,c_16])).

tff(c_32,plain,(
    ! [A_42,B_43,C_44] :
      ( k8_relset_1(A_42,B_43,C_44,B_43) = k1_relset_1(A_42,B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3127,plain,(
    k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3060,c_32])).

tff(c_5775,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3130,c_3133,c_3127])).

tff(c_5776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2952,c_5775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:02:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.18  
% 5.96/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.18  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k6_relset_1 > k5_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.96/2.18  
% 5.96/2.18  %Foreground sorts:
% 5.96/2.18  
% 5.96/2.18  
% 5.96/2.18  %Background operators:
% 5.96/2.18  
% 5.96/2.18  
% 5.96/2.18  %Foreground operators:
% 5.96/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.96/2.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.96/2.18  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.96/2.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.96/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.96/2.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.96/2.18  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 5.96/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.96/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.96/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.96/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.96/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.96/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.96/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.96/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.96/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.96/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.96/2.18  
% 5.96/2.20  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 5.96/2.20  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.96/2.20  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.96/2.20  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 5.96/2.20  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.96/2.20  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.96/2.20  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.96/2.20  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.96/2.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.96/2.20  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.96/2.20  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 5.96/2.20  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 5.96/2.20  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 5.96/2.20  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 5.96/2.20  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 5.96/2.20  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.96/2.20  tff(c_2864, plain, (![A_283, B_284, C_285, D_286]: (k7_relset_1(A_283, B_284, C_285, D_286)=k9_relat_1(C_285, D_286) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.96/2.20  tff(c_2867, plain, (![D_286]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_286)=k9_relat_1('#skF_3', D_286))), inference(resolution, [status(thm)], [c_38, c_2864])).
% 5.96/2.20  tff(c_2840, plain, (![A_277, B_278, C_279]: (k2_relset_1(A_277, B_278, C_279)=k2_relat_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.96/2.20  tff(c_2844, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_2840])).
% 5.96/2.20  tff(c_2947, plain, (![A_303, B_304, C_305]: (k7_relset_1(A_303, B_304, C_305, A_303)=k2_relset_1(A_303, B_304, C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.96/2.20  tff(c_2949, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_2947])).
% 5.96/2.20  tff(c_2951, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2867, c_2844, c_2949])).
% 5.96/2.20  tff(c_2902, plain, (![A_293, B_294, C_295, D_296]: (k8_relset_1(A_293, B_294, C_295, D_296)=k10_relat_1(C_295, D_296) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.96/2.20  tff(c_2905, plain, (![D_296]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_296)=k10_relat_1('#skF_3', D_296))), inference(resolution, [status(thm)], [c_38, c_2902])).
% 5.96/2.20  tff(c_2849, plain, (![A_280, B_281, C_282]: (k1_relset_1(A_280, B_281, C_282)=k1_relat_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.96/2.20  tff(c_2853, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_2849])).
% 5.96/2.20  tff(c_132, plain, (![A_74, B_75, C_76, D_77]: (k8_relset_1(A_74, B_75, C_76, D_77)=k10_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.96/2.20  tff(c_135, plain, (![D_77]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_77)=k10_relat_1('#skF_3', D_77))), inference(resolution, [status(thm)], [c_38, c_132])).
% 5.96/2.20  tff(c_96, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.96/2.20  tff(c_100, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_96])).
% 5.96/2.20  tff(c_169, plain, (![A_87, B_88, C_89]: (k8_relset_1(A_87, B_88, C_89, B_88)=k1_relset_1(A_87, B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.96/2.20  tff(c_171, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_169])).
% 5.96/2.20  tff(c_173, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_100, c_171])).
% 5.96/2.20  tff(c_146, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.96/2.20  tff(c_149, plain, (![D_82]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_82)=k9_relat_1('#skF_3', D_82))), inference(resolution, [status(thm)], [c_38, c_146])).
% 5.96/2.20  tff(c_87, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.96/2.20  tff(c_91, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_87])).
% 5.96/2.20  tff(c_36, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.96/2.20  tff(c_77, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 5.96/2.20  tff(c_105, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_77])).
% 5.96/2.20  tff(c_136, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_105])).
% 5.96/2.20  tff(c_150, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_136])).
% 5.96/2.20  tff(c_174, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_150])).
% 5.96/2.20  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.96/2.20  tff(c_42, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.96/2.20  tff(c_45, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_42])).
% 5.96/2.20  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 5.96/2.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.96/2.20  tff(c_56, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(k1_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.96/2.20  tff(c_61, plain, (![B_52]: (k7_relat_1(B_52, k1_relat_1(B_52))=B_52 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_6, c_56])).
% 5.96/2.20  tff(c_106, plain, (![A_64, B_65, C_66, D_67]: (k5_relset_1(A_64, B_65, C_66, D_67)=k7_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.96/2.20  tff(c_109, plain, (![D_67]: (k5_relset_1('#skF_2', '#skF_1', '#skF_3', D_67)=k7_relat_1('#skF_3', D_67))), inference(resolution, [status(thm)], [c_38, c_106])).
% 5.96/2.20  tff(c_295, plain, (![A_96, C_97, D_98, B_99]: (m1_subset_1(k5_relset_1(A_96, C_97, D_98, B_99), k1_zfmisc_1(k2_zfmisc_1(B_99, C_97))) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_96, C_97))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.96/2.20  tff(c_319, plain, (![D_67]: (m1_subset_1(k7_relat_1('#skF_3', D_67), k1_zfmisc_1(k2_zfmisc_1(D_67, '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_109, c_295])).
% 5.96/2.20  tff(c_341, plain, (![D_100]: (m1_subset_1(k7_relat_1('#skF_3', D_100), k1_zfmisc_1(k2_zfmisc_1(D_100, '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_319])).
% 5.96/2.20  tff(c_366, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_341])).
% 5.96/2.20  tff(c_379, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_366])).
% 5.96/2.20  tff(c_24, plain, (![A_26, B_27, C_28, D_29]: (k7_relset_1(A_26, B_27, C_28, D_29)=k9_relat_1(C_28, D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.96/2.20  tff(c_425, plain, (![D_29]: (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', D_29)=k9_relat_1('#skF_3', D_29))), inference(resolution, [status(thm)], [c_379, c_24])).
% 5.96/2.20  tff(c_18, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.96/2.20  tff(c_430, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_379, c_18])).
% 5.96/2.20  tff(c_34, plain, (![A_42, B_43, C_44]: (k7_relset_1(A_42, B_43, C_44, A_42)=k2_relset_1(A_42, B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.96/2.20  tff(c_424, plain, (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', k1_relat_1('#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_379, c_34])).
% 5.96/2.20  tff(c_2827, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_430, c_424])).
% 5.96/2.20  tff(c_2828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_2827])).
% 5.96/2.20  tff(c_2829, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 5.96/2.20  tff(c_2863, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2853, c_2829])).
% 5.96/2.20  tff(c_2868, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2867, c_2863])).
% 5.96/2.20  tff(c_2907, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2905, c_2868])).
% 5.96/2.20  tff(c_2952, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2951, c_2907])).
% 5.96/2.20  tff(c_71, plain, (![A_55, B_56]: (k8_relat_1(A_55, B_56)=B_56 | ~r1_tarski(k2_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.96/2.20  tff(c_76, plain, (![B_56]: (k8_relat_1(k2_relat_1(B_56), B_56)=B_56 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_6, c_71])).
% 5.96/2.20  tff(c_2888, plain, (![A_288, B_289, C_290, D_291]: (k6_relset_1(A_288, B_289, C_290, D_291)=k8_relat_1(C_290, D_291) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.96/2.20  tff(c_2891, plain, (![C_290]: (k6_relset_1('#skF_2', '#skF_1', C_290, '#skF_3')=k8_relat_1(C_290, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_2888])).
% 5.96/2.20  tff(c_2984, plain, (![C_309, A_310, B_311, D_312]: (m1_subset_1(k6_relset_1(C_309, A_310, B_311, D_312), k1_zfmisc_1(k2_zfmisc_1(C_309, B_311))) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(C_309, A_310))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.96/2.20  tff(c_3008, plain, (![C_290]: (m1_subset_1(k8_relat_1(C_290, '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', C_290))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2891, c_2984])).
% 5.96/2.20  tff(c_3022, plain, (![C_313]: (m1_subset_1(k8_relat_1(C_313, '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', C_313))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3008])).
% 5.96/2.20  tff(c_3047, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_3')))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_76, c_3022])).
% 5.96/2.20  tff(c_3060, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3047])).
% 5.96/2.20  tff(c_26, plain, (![A_30, B_31, C_32, D_33]: (k8_relset_1(A_30, B_31, C_32, D_33)=k10_relat_1(C_32, D_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.96/2.20  tff(c_3130, plain, (![D_33]: (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', D_33)=k10_relat_1('#skF_3', D_33))), inference(resolution, [status(thm)], [c_3060, c_26])).
% 5.96/2.20  tff(c_16, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.96/2.20  tff(c_3133, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3060, c_16])).
% 5.96/2.20  tff(c_32, plain, (![A_42, B_43, C_44]: (k8_relset_1(A_42, B_43, C_44, B_43)=k1_relset_1(A_42, B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.96/2.20  tff(c_3127, plain, (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_3060, c_32])).
% 5.96/2.20  tff(c_5775, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3130, c_3133, c_3127])).
% 5.96/2.20  tff(c_5776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2952, c_5775])).
% 5.96/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.20  
% 5.96/2.20  Inference rules
% 5.96/2.20  ----------------------
% 5.96/2.20  #Ref     : 0
% 5.96/2.20  #Sup     : 1414
% 5.96/2.20  #Fact    : 0
% 5.96/2.20  #Define  : 0
% 5.96/2.20  #Split   : 1
% 5.96/2.20  #Chain   : 0
% 5.96/2.20  #Close   : 0
% 5.96/2.20  
% 5.96/2.20  Ordering : KBO
% 5.96/2.20  
% 5.96/2.20  Simplification rules
% 5.96/2.20  ----------------------
% 5.96/2.20  #Subsume      : 0
% 5.96/2.20  #Demod        : 1211
% 5.96/2.20  #Tautology    : 671
% 5.96/2.20  #SimpNegUnit  : 2
% 5.96/2.20  #BackRed      : 33
% 5.96/2.20  
% 5.96/2.20  #Partial instantiations: 0
% 5.96/2.20  #Strategies tried      : 1
% 5.96/2.20  
% 5.96/2.20  Timing (in seconds)
% 5.96/2.20  ----------------------
% 5.96/2.20  Preprocessing        : 0.34
% 5.96/2.20  Parsing              : 0.19
% 5.96/2.20  CNF conversion       : 0.02
% 5.96/2.20  Main loop            : 1.09
% 5.96/2.20  Inferencing          : 0.36
% 5.96/2.20  Reduction            : 0.42
% 5.96/2.20  Demodulation         : 0.33
% 5.96/2.20  BG Simplification    : 0.05
% 5.96/2.20  Subsumption          : 0.14
% 5.96/2.20  Abstraction          : 0.09
% 5.96/2.20  MUC search           : 0.00
% 5.96/2.20  Cooper               : 0.00
% 5.96/2.20  Total                : 1.46
% 5.96/2.20  Index Insertion      : 0.00
% 5.96/2.20  Index Deletion       : 0.00
% 5.96/2.20  Index Matching       : 0.00
% 5.96/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
