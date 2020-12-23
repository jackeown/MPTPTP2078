%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:55 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 121 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 200 expanded)
%              Number of equality atoms :   40 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1094,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k8_relset_1(A_218,B_219,C_220,D_221) = k10_relat_1(C_220,D_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1109,plain,(
    ! [D_221] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_221) = k10_relat_1('#skF_3',D_221) ),
    inference(resolution,[status(thm)],[c_42,c_1094])).

tff(c_818,plain,(
    ! [A_188,B_189,C_190] :
      ( k1_relset_1(A_188,B_189,C_190) = k1_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_827,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_818])).

tff(c_324,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_339,plain,(
    ! [D_96] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_96) = k9_relat_1('#skF_3',D_96) ),
    inference(resolution,[status(thm)],[c_42,c_324])).

tff(c_188,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_197,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_78,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_198,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_78])).

tff(c_341,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_198])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_56])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_136,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_280,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k1_relset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_300,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_280])).

tff(c_306,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_300])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_314,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_306,c_8])).

tff(c_18,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_174,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k9_relat_1(C_73,A_74),k9_relat_1(C_73,B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_687,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(k2_relat_1(A_166),k9_relat_1(A_166,B_167))
      | ~ r1_tarski(k1_relat_1(A_166),B_167)
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_174])).

tff(c_110,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k9_relat_1(B_58,A_59),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [B_58,A_59] :
      ( k9_relat_1(B_58,A_59) = k2_relat_1(B_58)
      | ~ r1_tarski(k2_relat_1(B_58),k9_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_704,plain,(
    ! [A_168,B_169] :
      ( k9_relat_1(A_168,B_169) = k2_relat_1(A_168)
      | ~ r1_tarski(k1_relat_1(A_168),B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_687,c_116])).

tff(c_710,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_314,c_704])).

tff(c_720,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_710])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_720])).

tff(c_723,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_828,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_723])).

tff(c_1110,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_828])).

tff(c_853,plain,(
    ! [A_196,B_197,C_198] :
      ( k2_relset_1(A_196,B_197,C_198) = k2_relat_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_862,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_853])).

tff(c_883,plain,(
    ! [A_202,B_203,C_204] :
      ( m1_subset_1(k2_relset_1(A_202,B_203,C_204),k1_zfmisc_1(B_203))
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_900,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_883])).

tff(c_906,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_900])).

tff(c_914,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_906,c_8])).

tff(c_24,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_782,plain,(
    ! [C_178,A_179,B_180] :
      ( r1_tarski(k10_relat_1(C_178,A_179),k10_relat_1(C_178,B_180))
      | ~ r1_tarski(A_179,B_180)
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1880,plain,(
    ! [A_319,B_320] :
      ( r1_tarski(k1_relat_1(A_319),k10_relat_1(A_319,B_320))
      | ~ r1_tarski(k2_relat_1(A_319),B_320)
      | ~ v1_relat_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_782])).

tff(c_748,plain,(
    ! [B_173,A_174] :
      ( r1_tarski(k10_relat_1(B_173,A_174),k1_relat_1(B_173))
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_757,plain,(
    ! [B_173,A_174] :
      ( k10_relat_1(B_173,A_174) = k1_relat_1(B_173)
      | ~ r1_tarski(k1_relat_1(B_173),k10_relat_1(B_173,A_174))
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_748,c_2])).

tff(c_1932,plain,(
    ! [A_322,B_323] :
      ( k10_relat_1(A_322,B_323) = k1_relat_1(A_322)
      | ~ r1_tarski(k2_relat_1(A_322),B_323)
      | ~ v1_relat_1(A_322) ) ),
    inference(resolution,[status(thm)],[c_1880,c_757])).

tff(c_1950,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_914,c_1932])).

tff(c_1970,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1950])).

tff(c_1972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_1970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.72  
% 3.78/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.72  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.78/1.72  
% 3.78/1.72  %Foreground sorts:
% 3.78/1.72  
% 3.78/1.72  
% 3.78/1.72  %Background operators:
% 3.78/1.72  
% 3.78/1.72  
% 3.78/1.72  %Foreground operators:
% 3.78/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.72  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.78/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.78/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.78/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.78/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.78/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.78/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.78/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.78/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.78/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.72  
% 3.78/1.74  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.78/1.74  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.78/1.74  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.78/1.74  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.78/1.74  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.78/1.74  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.78/1.74  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.78/1.74  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.78/1.74  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.78/1.74  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.78/1.74  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.78/1.74  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.78/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.78/1.74  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.78/1.74  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.78/1.74  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.78/1.74  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.78/1.74  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.78/1.74  tff(c_1094, plain, (![A_218, B_219, C_220, D_221]: (k8_relset_1(A_218, B_219, C_220, D_221)=k10_relat_1(C_220, D_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.78/1.74  tff(c_1109, plain, (![D_221]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_221)=k10_relat_1('#skF_3', D_221))), inference(resolution, [status(thm)], [c_42, c_1094])).
% 3.78/1.74  tff(c_818, plain, (![A_188, B_189, C_190]: (k1_relset_1(A_188, B_189, C_190)=k1_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.78/1.74  tff(c_827, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_818])).
% 3.78/1.74  tff(c_324, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.78/1.74  tff(c_339, plain, (![D_96]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_96)=k9_relat_1('#skF_3', D_96))), inference(resolution, [status(thm)], [c_42, c_324])).
% 3.78/1.74  tff(c_188, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.78/1.74  tff(c_197, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_188])).
% 3.78/1.74  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.78/1.74  tff(c_78, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.78/1.74  tff(c_198, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_78])).
% 3.78/1.74  tff(c_341, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_198])).
% 3.78/1.74  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.78/1.74  tff(c_56, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.78/1.74  tff(c_62, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_56])).
% 3.78/1.74  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 3.78/1.74  tff(c_136, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.78/1.74  tff(c_145, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_136])).
% 3.78/1.74  tff(c_280, plain, (![A_90, B_91, C_92]: (m1_subset_1(k1_relset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.78/1.74  tff(c_300, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_145, c_280])).
% 3.78/1.74  tff(c_306, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_300])).
% 3.78/1.74  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.74  tff(c_314, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_306, c_8])).
% 3.78/1.74  tff(c_18, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.78/1.74  tff(c_174, plain, (![C_73, A_74, B_75]: (r1_tarski(k9_relat_1(C_73, A_74), k9_relat_1(C_73, B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.78/1.74  tff(c_687, plain, (![A_166, B_167]: (r1_tarski(k2_relat_1(A_166), k9_relat_1(A_166, B_167)) | ~r1_tarski(k1_relat_1(A_166), B_167) | ~v1_relat_1(A_166) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_18, c_174])).
% 3.78/1.74  tff(c_110, plain, (![B_58, A_59]: (r1_tarski(k9_relat_1(B_58, A_59), k2_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.78/1.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.78/1.74  tff(c_116, plain, (![B_58, A_59]: (k9_relat_1(B_58, A_59)=k2_relat_1(B_58) | ~r1_tarski(k2_relat_1(B_58), k9_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.78/1.74  tff(c_704, plain, (![A_168, B_169]: (k9_relat_1(A_168, B_169)=k2_relat_1(A_168) | ~r1_tarski(k1_relat_1(A_168), B_169) | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_687, c_116])).
% 3.78/1.74  tff(c_710, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_314, c_704])).
% 3.78/1.74  tff(c_720, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_710])).
% 3.78/1.74  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_341, c_720])).
% 3.78/1.74  tff(c_723, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.78/1.74  tff(c_828, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_723])).
% 3.78/1.74  tff(c_1110, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_828])).
% 3.78/1.74  tff(c_853, plain, (![A_196, B_197, C_198]: (k2_relset_1(A_196, B_197, C_198)=k2_relat_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.78/1.74  tff(c_862, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_853])).
% 3.78/1.74  tff(c_883, plain, (![A_202, B_203, C_204]: (m1_subset_1(k2_relset_1(A_202, B_203, C_204), k1_zfmisc_1(B_203)) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.78/1.74  tff(c_900, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_862, c_883])).
% 3.78/1.74  tff(c_906, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_900])).
% 3.78/1.74  tff(c_914, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_906, c_8])).
% 3.78/1.74  tff(c_24, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.78/1.74  tff(c_782, plain, (![C_178, A_179, B_180]: (r1_tarski(k10_relat_1(C_178, A_179), k10_relat_1(C_178, B_180)) | ~r1_tarski(A_179, B_180) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.78/1.74  tff(c_1880, plain, (![A_319, B_320]: (r1_tarski(k1_relat_1(A_319), k10_relat_1(A_319, B_320)) | ~r1_tarski(k2_relat_1(A_319), B_320) | ~v1_relat_1(A_319) | ~v1_relat_1(A_319))), inference(superposition, [status(thm), theory('equality')], [c_24, c_782])).
% 3.78/1.74  tff(c_748, plain, (![B_173, A_174]: (r1_tarski(k10_relat_1(B_173, A_174), k1_relat_1(B_173)) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.74  tff(c_757, plain, (![B_173, A_174]: (k10_relat_1(B_173, A_174)=k1_relat_1(B_173) | ~r1_tarski(k1_relat_1(B_173), k10_relat_1(B_173, A_174)) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_748, c_2])).
% 3.78/1.74  tff(c_1932, plain, (![A_322, B_323]: (k10_relat_1(A_322, B_323)=k1_relat_1(A_322) | ~r1_tarski(k2_relat_1(A_322), B_323) | ~v1_relat_1(A_322))), inference(resolution, [status(thm)], [c_1880, c_757])).
% 3.78/1.74  tff(c_1950, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_914, c_1932])).
% 3.78/1.74  tff(c_1970, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1950])).
% 3.78/1.74  tff(c_1972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1110, c_1970])).
% 3.78/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.74  
% 3.78/1.74  Inference rules
% 3.78/1.74  ----------------------
% 3.78/1.74  #Ref     : 0
% 3.78/1.74  #Sup     : 410
% 3.78/1.74  #Fact    : 0
% 3.78/1.74  #Define  : 0
% 3.78/1.74  #Split   : 12
% 3.78/1.74  #Chain   : 0
% 3.78/1.74  #Close   : 0
% 3.78/1.74  
% 3.78/1.74  Ordering : KBO
% 3.78/1.74  
% 3.78/1.74  Simplification rules
% 3.78/1.74  ----------------------
% 3.78/1.74  #Subsume      : 61
% 3.78/1.74  #Demod        : 208
% 3.78/1.74  #Tautology    : 123
% 3.78/1.74  #SimpNegUnit  : 8
% 3.78/1.74  #BackRed      : 5
% 3.78/1.74  
% 3.78/1.74  #Partial instantiations: 0
% 3.78/1.74  #Strategies tried      : 1
% 3.78/1.74  
% 3.78/1.74  Timing (in seconds)
% 3.78/1.74  ----------------------
% 3.78/1.74  Preprocessing        : 0.34
% 3.78/1.74  Parsing              : 0.19
% 3.78/1.74  CNF conversion       : 0.02
% 3.78/1.74  Main loop            : 0.57
% 3.78/1.74  Inferencing          : 0.23
% 3.78/1.74  Reduction            : 0.16
% 3.78/1.74  Demodulation         : 0.11
% 3.78/1.74  BG Simplification    : 0.03
% 3.78/1.74  Subsumption          : 0.10
% 3.78/1.74  Abstraction          : 0.03
% 3.78/1.74  MUC search           : 0.00
% 3.78/1.74  Cooper               : 0.00
% 3.78/1.74  Total                : 0.94
% 3.78/1.74  Index Insertion      : 0.00
% 3.78/1.74  Index Deletion       : 0.00
% 3.78/1.74  Index Matching       : 0.00
% 3.78/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
