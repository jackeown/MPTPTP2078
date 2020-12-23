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
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 8.72s
% Output     : CNFRefutation 8.78s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 478 expanded)
%              Number of leaves         :   37 ( 170 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 ( 912 expanded)
%              Number of equality atoms :   22 (  87 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_75,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_81])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_15,B_16)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1253,plain,(
    ! [C_151,A_152,B_153] :
      ( m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ r1_tarski(k2_relat_1(C_151),B_153)
      | ~ r1_tarski(k1_relat_1(C_151),A_152)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_781,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k6_relset_1(A_121,B_122,C_123,D_124) = k8_relat_1(C_123,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_792,plain,(
    ! [C_123] : k6_relset_1('#skF_3','#skF_1',C_123,'#skF_4') = k8_relat_1(C_123,'#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_781])).

tff(c_44,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_794,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_44])).

tff(c_1281,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1253,c_794])).

tff(c_1343,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1349,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_1343])).

tff(c_1354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1349])).

tff(c_1355,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1688,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1355])).

tff(c_1694,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1688])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1694])).

tff(c_1702,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_17,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_148,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_139])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_226,plain,(
    ! [A_86,B_87] :
      ( k8_relat_1(A_86,B_87) = B_87
      | ~ r1_tarski(k2_relat_1(B_87),A_86)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_249,plain,(
    ! [A_93,B_94] :
      ( k8_relat_1(A_93,B_94) = B_94
      | ~ v5_relat_1(B_94,A_93)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_12,c_226])).

tff(c_258,plain,
    ( k8_relat_1('#skF_1','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_249])).

tff(c_263,plain,(
    k8_relat_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_258])).

tff(c_270,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_18])).

tff(c_279,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_270])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_374,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,'#skF_1')
      | ~ r1_tarski(A_98,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_279,c_2])).

tff(c_385,plain,(
    ! [A_17] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_17,'#skF_4')),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_374])).

tff(c_395,plain,(
    ! [A_17] : r1_tarski(k2_relat_1(k8_relat_1(A_17,'#skF_4')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_385])).

tff(c_1356,plain,(
    v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_1703,plain,(
    r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_24,plain,(
    ! [A_21] :
      ( k8_relat_1(k2_relat_1(A_21),A_21) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_672,plain,(
    ! [A_114,B_115,C_116] :
      ( k8_relat_1(A_114,k8_relat_1(B_115,C_116)) = k8_relat_1(A_114,C_116)
      | ~ r1_tarski(A_114,B_115)
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10133,plain,(
    ! [B_497,C_498] :
      ( k8_relat_1(k2_relat_1(k8_relat_1(B_497,C_498)),C_498) = k8_relat_1(B_497,C_498)
      | ~ r1_tarski(k2_relat_1(k8_relat_1(B_497,C_498)),B_497)
      | ~ v1_relat_1(C_498)
      | ~ v1_relat_1(k8_relat_1(B_497,C_498)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_672])).

tff(c_10198,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_4') = k8_relat_1('#skF_2','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1703,c_10133])).

tff(c_10279,plain,(
    k8_relat_1(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_4') = k8_relat_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_85,c_10198])).

tff(c_448,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(k8_relat_1(A_101,C_102),k8_relat_1(B_103,C_102))
      | ~ r1_tarski(A_101,B_103)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_465,plain,(
    ! [A_101] :
      ( r1_tarski(k8_relat_1(A_101,'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_101,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_448])).

tff(c_546,plain,(
    ! [A_108] :
      ( r1_tarski(k8_relat_1(A_108,'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_108,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_465])).

tff(c_566,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_546])).

tff(c_576,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_279,c_566])).

tff(c_50,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_50])).

tff(c_179,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(A_81,C_82)
      | ~ r1_tarski(B_83,C_82)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_84,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_179])).

tff(c_208,plain,(
    ! [A_1,A_84] :
      ( r1_tarski(A_1,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_1,A_84)
      | ~ r1_tarski(A_84,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_192,c_2])).

tff(c_567,plain,(
    ! [A_108] :
      ( r1_tarski(k8_relat_1(A_108,'#skF_4'),k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski(A_108,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_546,c_208])).

tff(c_7977,plain,(
    ! [A_108] :
      ( r1_tarski(k8_relat_1(A_108,'#skF_4'),k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_108,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_567])).

tff(c_10324,plain,
    ( r1_tarski(k8_relat_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10279,c_7977])).

tff(c_10463,plain,(
    r1_tarski(k8_relat_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_10324])).

tff(c_481,plain,(
    ! [A_101] :
      ( r1_tarski(k8_relat_1(A_101,'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_101,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_465])).

tff(c_191,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_179])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_321,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1450,plain,(
    ! [A_164,B_165,A_166] :
      ( k1_relset_1(A_164,B_165,A_166) = k1_relat_1(A_166)
      | ~ r1_tarski(A_166,k2_zfmisc_1(A_164,B_165)) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_1470,plain,(
    ! [A_167] :
      ( k1_relset_1('#skF_3','#skF_1',A_167) = k1_relat_1(A_167)
      | ~ r1_tarski(A_167,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_191,c_1450])).

tff(c_1491,plain,(
    ! [A_101] :
      ( k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_101,'#skF_4')) = k1_relat_1(k8_relat_1(A_101,'#skF_4'))
      | ~ r1_tarski(A_101,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_481,c_1470])).

tff(c_10336,plain,
    ( k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_4')) = k1_relset_1('#skF_3','#skF_1',k8_relat_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10279,c_1491])).

tff(c_10471,plain,(
    k1_relset_1('#skF_3','#skF_1',k8_relat_1('#skF_2','#skF_4')) = k1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_10279,c_10336])).

tff(c_577,plain,(
    ! [A_109,B_110,C_111] :
      ( m1_subset_1(k1_relset_1(A_109,B_110,C_111),k1_zfmisc_1(A_109))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2277,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_tarski(k1_relset_1(A_200,B_201,C_202),A_200)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(resolution,[status(thm)],[c_577,c_4])).

tff(c_2290,plain,(
    ! [A_200,B_201,A_4] :
      ( r1_tarski(k1_relset_1(A_200,B_201,A_4),A_200)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_200,B_201)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2277])).

tff(c_11956,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10471,c_2290])).

tff(c_11969,plain,(
    r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10463,c_11956])).

tff(c_11971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_11969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.72/3.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.19  
% 8.78/3.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.19  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.78/3.19  
% 8.78/3.19  %Foreground sorts:
% 8.78/3.19  
% 8.78/3.19  
% 8.78/3.19  %Background operators:
% 8.78/3.19  
% 8.78/3.19  
% 8.78/3.19  %Foreground operators:
% 8.78/3.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.78/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.78/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.78/3.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.78/3.19  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 8.78/3.19  tff('#skF_2', type, '#skF_2': $i).
% 8.78/3.19  tff('#skF_3', type, '#skF_3': $i).
% 8.78/3.19  tff('#skF_1', type, '#skF_1': $i).
% 8.78/3.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.78/3.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.78/3.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.78/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.78/3.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.78/3.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.78/3.19  tff('#skF_4', type, '#skF_4': $i).
% 8.78/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.78/3.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.78/3.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.78/3.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.78/3.19  
% 8.78/3.21  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.78/3.21  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 8.78/3.21  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.78/3.21  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 8.78/3.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 8.78/3.21  tff(f_110, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.78/3.21  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 8.78/3.21  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_relat_1)).
% 8.78/3.21  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.78/3.21  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.78/3.21  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 8.78/3.21  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.78/3.21  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 8.78/3.21  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 8.78/3.21  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 8.78/3.21  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.78/3.21  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.78/3.21  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 8.78/3.21  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.78/3.21  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.78/3.21  tff(c_75, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.78/3.21  tff(c_81, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_75])).
% 8.78/3.21  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_81])).
% 8.78/3.21  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k2_relat_1(k8_relat_1(A_15, B_16)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.78/3.21  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.78/3.21  tff(c_1253, plain, (![C_151, A_152, B_153]: (m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~r1_tarski(k2_relat_1(C_151), B_153) | ~r1_tarski(k1_relat_1(C_151), A_152) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.78/3.21  tff(c_781, plain, (![A_121, B_122, C_123, D_124]: (k6_relset_1(A_121, B_122, C_123, D_124)=k8_relat_1(C_123, D_124) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.78/3.21  tff(c_792, plain, (![C_123]: (k6_relset_1('#skF_3', '#skF_1', C_123, '#skF_4')=k8_relat_1(C_123, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_781])).
% 8.78/3.21  tff(c_44, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.78/3.21  tff(c_794, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_44])).
% 8.78/3.21  tff(c_1281, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_1253, c_794])).
% 8.78/3.21  tff(c_1343, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1281])).
% 8.78/3.21  tff(c_1349, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_1343])).
% 8.78/3.21  tff(c_1354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_1349])).
% 8.78/3.21  tff(c_1355, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_1281])).
% 8.78/3.21  tff(c_1688, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1355])).
% 8.78/3.21  tff(c_1694, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1688])).
% 8.78/3.21  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_1694])).
% 8.78/3.21  tff(c_1702, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_1355])).
% 8.78/3.21  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k2_relat_1(k8_relat_1(A_17, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.78/3.21  tff(c_139, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.78/3.21  tff(c_148, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_139])).
% 8.78/3.21  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.78/3.21  tff(c_226, plain, (![A_86, B_87]: (k8_relat_1(A_86, B_87)=B_87 | ~r1_tarski(k2_relat_1(B_87), A_86) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.78/3.21  tff(c_249, plain, (![A_93, B_94]: (k8_relat_1(A_93, B_94)=B_94 | ~v5_relat_1(B_94, A_93) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_12, c_226])).
% 8.78/3.21  tff(c_258, plain, (k8_relat_1('#skF_1', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_148, c_249])).
% 8.78/3.21  tff(c_263, plain, (k8_relat_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_258])).
% 8.78/3.21  tff(c_270, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_263, c_18])).
% 8.78/3.21  tff(c_279, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_270])).
% 8.78/3.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.21  tff(c_374, plain, (![A_98]: (r1_tarski(A_98, '#skF_1') | ~r1_tarski(A_98, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_279, c_2])).
% 8.78/3.21  tff(c_385, plain, (![A_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_17, '#skF_4')), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_374])).
% 8.78/3.21  tff(c_395, plain, (![A_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_17, '#skF_4')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_385])).
% 8.78/3.21  tff(c_1356, plain, (v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_1281])).
% 8.78/3.21  tff(c_1703, plain, (r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_1355])).
% 8.78/3.21  tff(c_24, plain, (![A_21]: (k8_relat_1(k2_relat_1(A_21), A_21)=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.78/3.21  tff(c_672, plain, (![A_114, B_115, C_116]: (k8_relat_1(A_114, k8_relat_1(B_115, C_116))=k8_relat_1(A_114, C_116) | ~r1_tarski(A_114, B_115) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.78/3.21  tff(c_10133, plain, (![B_497, C_498]: (k8_relat_1(k2_relat_1(k8_relat_1(B_497, C_498)), C_498)=k8_relat_1(B_497, C_498) | ~r1_tarski(k2_relat_1(k8_relat_1(B_497, C_498)), B_497) | ~v1_relat_1(C_498) | ~v1_relat_1(k8_relat_1(B_497, C_498)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_672])).
% 8.78/3.21  tff(c_10198, plain, (k8_relat_1(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_4')=k8_relat_1('#skF_2', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_1703, c_10133])).
% 8.78/3.21  tff(c_10279, plain, (k8_relat_1(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_4')=k8_relat_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_85, c_10198])).
% 8.78/3.21  tff(c_448, plain, (![A_101, C_102, B_103]: (r1_tarski(k8_relat_1(A_101, C_102), k8_relat_1(B_103, C_102)) | ~r1_tarski(A_101, B_103) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.78/3.21  tff(c_465, plain, (![A_101]: (r1_tarski(k8_relat_1(A_101, '#skF_4'), '#skF_4') | ~r1_tarski(A_101, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_448])).
% 8.78/3.21  tff(c_546, plain, (![A_108]: (r1_tarski(k8_relat_1(A_108, '#skF_4'), '#skF_4') | ~r1_tarski(A_108, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_465])).
% 8.78/3.21  tff(c_566, plain, (r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24, c_546])).
% 8.78/3.21  tff(c_576, plain, (r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_279, c_566])).
% 8.78/3.21  tff(c_50, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.21  tff(c_58, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_50])).
% 8.78/3.21  tff(c_179, plain, (![A_81, C_82, B_83]: (r1_tarski(A_81, C_82) | ~r1_tarski(B_83, C_82) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.78/3.21  tff(c_192, plain, (![A_84]: (r1_tarski(A_84, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_84, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_179])).
% 8.78/3.21  tff(c_208, plain, (![A_1, A_84]: (r1_tarski(A_1, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_1, A_84) | ~r1_tarski(A_84, '#skF_4'))), inference(resolution, [status(thm)], [c_192, c_2])).
% 8.78/3.21  tff(c_567, plain, (![A_108]: (r1_tarski(k8_relat_1(A_108, '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(A_108, '#skF_1'))), inference(resolution, [status(thm)], [c_546, c_208])).
% 8.78/3.21  tff(c_7977, plain, (![A_108]: (r1_tarski(k8_relat_1(A_108, '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_108, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_567])).
% 8.78/3.21  tff(c_10324, plain, (r1_tarski(k8_relat_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10279, c_7977])).
% 8.78/3.21  tff(c_10463, plain, (r1_tarski(k8_relat_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_10324])).
% 8.78/3.21  tff(c_481, plain, (![A_101]: (r1_tarski(k8_relat_1(A_101, '#skF_4'), '#skF_4') | ~r1_tarski(A_101, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_465])).
% 8.78/3.21  tff(c_191, plain, (![A_81]: (r1_tarski(A_81, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_81, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_179])).
% 8.78/3.21  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.21  tff(c_321, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.78/3.21  tff(c_1450, plain, (![A_164, B_165, A_166]: (k1_relset_1(A_164, B_165, A_166)=k1_relat_1(A_166) | ~r1_tarski(A_166, k2_zfmisc_1(A_164, B_165)))), inference(resolution, [status(thm)], [c_6, c_321])).
% 8.78/3.21  tff(c_1470, plain, (![A_167]: (k1_relset_1('#skF_3', '#skF_1', A_167)=k1_relat_1(A_167) | ~r1_tarski(A_167, '#skF_4'))), inference(resolution, [status(thm)], [c_191, c_1450])).
% 8.78/3.21  tff(c_1491, plain, (![A_101]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_101, '#skF_4'))=k1_relat_1(k8_relat_1(A_101, '#skF_4')) | ~r1_tarski(A_101, '#skF_1'))), inference(resolution, [status(thm)], [c_481, c_1470])).
% 8.78/3.21  tff(c_10336, plain, (k1_relat_1(k8_relat_1(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_4'))=k1_relset_1('#skF_3', '#skF_1', k8_relat_1('#skF_2', '#skF_4')) | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10279, c_1491])).
% 8.78/3.21  tff(c_10471, plain, (k1_relset_1('#skF_3', '#skF_1', k8_relat_1('#skF_2', '#skF_4'))=k1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_10279, c_10336])).
% 8.78/3.21  tff(c_577, plain, (![A_109, B_110, C_111]: (m1_subset_1(k1_relset_1(A_109, B_110, C_111), k1_zfmisc_1(A_109)) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.78/3.21  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.78/3.21  tff(c_2277, plain, (![A_200, B_201, C_202]: (r1_tarski(k1_relset_1(A_200, B_201, C_202), A_200) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(resolution, [status(thm)], [c_577, c_4])).
% 8.78/3.21  tff(c_2290, plain, (![A_200, B_201, A_4]: (r1_tarski(k1_relset_1(A_200, B_201, A_4), A_200) | ~r1_tarski(A_4, k2_zfmisc_1(A_200, B_201)))), inference(resolution, [status(thm)], [c_6, c_2277])).
% 8.78/3.21  tff(c_11956, plain, (r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10471, c_2290])).
% 8.78/3.21  tff(c_11969, plain, (r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10463, c_11956])).
% 8.78/3.21  tff(c_11971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_11969])).
% 8.78/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.78/3.21  
% 8.78/3.21  Inference rules
% 8.78/3.21  ----------------------
% 8.78/3.21  #Ref     : 0
% 8.78/3.21  #Sup     : 2590
% 8.78/3.21  #Fact    : 0
% 8.78/3.21  #Define  : 0
% 8.78/3.21  #Split   : 19
% 8.78/3.21  #Chain   : 0
% 8.78/3.21  #Close   : 0
% 8.78/3.21  
% 8.78/3.21  Ordering : KBO
% 8.78/3.21  
% 8.78/3.21  Simplification rules
% 8.78/3.21  ----------------------
% 8.78/3.21  #Subsume      : 463
% 8.78/3.21  #Demod        : 1786
% 8.78/3.21  #Tautology    : 587
% 8.78/3.21  #SimpNegUnit  : 7
% 8.78/3.21  #BackRed      : 2
% 8.78/3.21  
% 8.78/3.21  #Partial instantiations: 0
% 8.78/3.21  #Strategies tried      : 1
% 8.78/3.21  
% 8.78/3.21  Timing (in seconds)
% 8.78/3.21  ----------------------
% 8.78/3.21  Preprocessing        : 0.32
% 8.78/3.21  Parsing              : 0.18
% 8.78/3.21  CNF conversion       : 0.02
% 8.78/3.21  Main loop            : 2.08
% 8.78/3.21  Inferencing          : 0.58
% 8.78/3.21  Reduction            : 0.80
% 8.78/3.21  Demodulation         : 0.59
% 8.78/3.21  BG Simplification    : 0.06
% 8.78/3.21  Subsumption          : 0.50
% 8.78/3.21  Abstraction          : 0.08
% 8.78/3.21  MUC search           : 0.00
% 8.78/3.21  Cooper               : 0.00
% 8.78/3.21  Total                : 2.44
% 8.78/3.21  Index Insertion      : 0.00
% 8.78/3.21  Index Deletion       : 0.00
% 8.90/3.21  Index Matching       : 0.00
% 8.90/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
