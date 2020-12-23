%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 9.43s
% Verified   : 
% Statistics : Number of formulae       :  243 (1711 expanded)
%              Number of leaves         :   50 ( 577 expanded)
%              Depth                    :   16
%              Number of atoms          :  419 (3447 expanded)
%              Number of equality atoms :  189 (1544 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1503,plain,(
    ! [C_214,A_215,B_216] :
      ( v1_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1516,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1503])).

tff(c_2395,plain,(
    ! [A_311,B_312,C_313,D_314] :
      ( k8_relset_1(A_311,B_312,C_313,D_314) = k10_relat_1(C_313,D_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2406,plain,(
    ! [D_314] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_314) = k10_relat_1('#skF_3',D_314) ),
    inference(resolution,[status(thm)],[c_70,c_2395])).

tff(c_2039,plain,(
    ! [A_291,B_292,C_293] :
      ( k1_relset_1(A_291,B_292,C_293) = k1_relat_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2054,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2039])).

tff(c_210,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_223,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_210])).

tff(c_314,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_329,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_314])).

tff(c_545,plain,(
    ! [B_131,A_132] :
      ( k7_relat_1(B_131,A_132) = B_131
      | ~ v4_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_560,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_545])).

tff(c_573,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_560])).

tff(c_594,plain,(
    ! [B_136,A_137] :
      ( k2_relat_1(k7_relat_1(B_136,A_137)) = k9_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_609,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_594])).

tff(c_617,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_609])).

tff(c_1429,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k7_relset_1(A_198,B_199,C_200,D_201) = k9_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1440,plain,(
    ! [D_201] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_201) = k9_relat_1('#skF_3',D_201) ),
    inference(resolution,[status(thm)],[c_70,c_1429])).

tff(c_985,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1000,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_985])).

tff(c_68,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_187,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1001,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_187])).

tff(c_1441,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_1001])).

tff(c_1444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_1441])).

tff(c_1445,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2055,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2054,c_1445])).

tff(c_2407,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2055])).

tff(c_40,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_128,plain,(
    ! [A_60] :
      ( k1_relat_1(A_60) != k1_xboole_0
      | k1_xboole_0 = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_137,plain,(
    ! [A_30] :
      ( k1_relat_1(k6_relat_1(A_30)) != k1_xboole_0
      | k6_relat_1(A_30) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_128])).

tff(c_144,plain,(
    ! [A_30] :
      ( k1_xboole_0 != A_30
      | k6_relat_1(A_30) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_137])).

tff(c_1730,plain,(
    ! [A_249,B_250] :
      ( k5_relat_1(k6_relat_1(A_249),B_250) = k7_relat_1(B_250,A_249)
      | ~ v1_relat_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9465,plain,(
    ! [B_588,A_589] :
      ( k7_relat_1(B_588,A_589) = k5_relat_1(k1_xboole_0,B_588)
      | ~ v1_relat_1(B_588)
      | k1_xboole_0 != A_589 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1730])).

tff(c_9631,plain,(
    ! [A_594] :
      ( k7_relat_1('#skF_3',A_594) = k5_relat_1(k1_xboole_0,'#skF_3')
      | k1_xboole_0 != A_594 ) ),
    inference(resolution,[status(thm)],[c_1516,c_9465])).

tff(c_1527,plain,(
    ! [C_217,A_218,B_219] :
      ( v4_relat_1(C_217,A_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1542,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_1527])).

tff(c_1798,plain,(
    ! [B_263,A_264] :
      ( k7_relat_1(B_263,A_264) = B_263
      | ~ v4_relat_1(B_263,A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1813,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1542,c_1798])).

tff(c_1826,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1813])).

tff(c_9647,plain,
    ( k5_relat_1(k1_xboole_0,'#skF_3') = '#skF_3'
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9631,c_1826])).

tff(c_9677,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9647])).

tff(c_182,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_186,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_182])).

tff(c_14,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k2_relat_1(k2_zfmisc_1(A_15,B_16)) = B_16
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2063,plain,(
    ! [A_294,B_295] :
      ( r1_tarski(k2_relat_1(A_294),k2_relat_1(B_295))
      | ~ r1_tarski(A_294,B_295)
      | ~ v1_relat_1(B_295)
      | ~ v1_relat_1(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2072,plain,(
    ! [A_294,B_16,A_15] :
      ( r1_tarski(k2_relat_1(A_294),B_16)
      | ~ r1_tarski(A_294,k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(k2_zfmisc_1(A_15,B_16))
      | ~ v1_relat_1(A_294)
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2063])).

tff(c_11197,plain,(
    ! [A_617,B_618,A_619] :
      ( r1_tarski(k2_relat_1(A_617),B_618)
      | ~ r1_tarski(A_617,k2_zfmisc_1(A_619,B_618))
      | ~ v1_relat_1(A_617)
      | k1_xboole_0 = B_618
      | k1_xboole_0 = A_619 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2072])).

tff(c_11232,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_186,c_11197])).

tff(c_11252,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_11232])).

tff(c_11253,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_9677,c_11252])).

tff(c_11255,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11253])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11395,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11255,c_11255,c_6])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2309,plain,(
    ! [A_306,B_307] :
      ( r1_tarski(k1_relat_1(A_306),k1_relat_1(B_307))
      | ~ r1_tarski(A_306,B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2321,plain,(
    ! [A_23,B_307] :
      ( r1_tarski(A_23,k1_relat_1(B_307))
      | ~ r1_tarski(k6_relat_1(A_23),B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2309])).

tff(c_2689,plain,(
    ! [A_335,B_336] :
      ( r1_tarski(A_335,k1_relat_1(B_336))
      | ~ r1_tarski(k6_relat_1(A_335),B_336)
      | ~ v1_relat_1(B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2321])).

tff(c_2700,plain,(
    ! [A_30,B_336] :
      ( r1_tarski(A_30,k1_relat_1(B_336))
      | ~ r1_tarski(k1_xboole_0,B_336)
      | ~ v1_relat_1(B_336)
      | k1_xboole_0 != A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2689])).

tff(c_2710,plain,(
    ! [A_337,B_338] :
      ( r1_tarski(A_337,k1_relat_1(B_338))
      | ~ v1_relat_1(B_338)
      | k1_xboole_0 != A_337 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2700])).

tff(c_2731,plain,(
    ! [A_337,A_23] :
      ( r1_tarski(A_337,A_23)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | k1_xboole_0 != A_337 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2710])).

tff(c_2741,plain,(
    ! [A_337,A_23] :
      ( r1_tarski(A_337,A_23)
      | k1_xboole_0 != A_337 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2731])).

tff(c_145,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_137])).

tff(c_89,plain,(
    ! [A_55,B_56] : v1_relat_1(k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_89])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2090,plain,(
    ! [A_294] :
      ( r1_tarski(k2_relat_1(A_294),k1_xboole_0)
      | ~ r1_tarski(A_294,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2063])).

tff(c_2104,plain,(
    ! [A_296] :
      ( r1_tarski(k2_relat_1(A_296),k1_xboole_0)
      | ~ r1_tarski(A_296,k1_xboole_0)
      | ~ v1_relat_1(A_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_2090])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k5_relat_1(B_25,k6_relat_1(A_24)) = B_25
      | ~ r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2107,plain,(
    ! [A_296] :
      ( k5_relat_1(A_296,k6_relat_1(k1_xboole_0)) = A_296
      | ~ r1_tarski(A_296,k1_xboole_0)
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_2104,c_44])).

tff(c_2945,plain,(
    ! [A_350] :
      ( k5_relat_1(A_350,k1_xboole_0) = A_350
      | ~ r1_tarski(A_350,k1_xboole_0)
      | ~ v1_relat_1(A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2107])).

tff(c_3010,plain,(
    ! [A_354] :
      ( k5_relat_1(A_354,k1_xboole_0) = A_354
      | ~ v1_relat_1(A_354)
      | k1_xboole_0 != A_354 ) ),
    inference(resolution,[status(thm)],[c_2741,c_2945])).

tff(c_3045,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) = '#skF_3'
    | k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1516,c_3010])).

tff(c_3048,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3045])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1660,plain,(
    ! [A_237,A_238,B_239] :
      ( v4_relat_1(A_237,A_238)
      | ~ r1_tarski(A_237,k2_zfmisc_1(A_238,B_239)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1527])).

tff(c_1686,plain,(
    ! [A_238] : v4_relat_1(k1_xboole_0,A_238) ),
    inference(resolution,[status(thm)],[c_2,c_1660])).

tff(c_1807,plain,(
    ! [A_238] :
      ( k7_relat_1(k1_xboole_0,A_238) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1686,c_1798])).

tff(c_1837,plain,(
    ! [A_266] : k7_relat_1(k1_xboole_0,A_266) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1807])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1842,plain,(
    ! [A_266] :
      ( k9_relat_1(k1_xboole_0,A_266) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1837,c_16])).

tff(c_1847,plain,(
    ! [A_266] : k9_relat_1(k1_xboole_0,A_266) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_32,c_1842])).

tff(c_42,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1950,plain,(
    ! [B_283,A_284] :
      ( k5_relat_1(B_283,k6_relat_1(A_284)) = B_283
      | ~ r1_tarski(k2_relat_1(B_283),A_284)
      | ~ v1_relat_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1959,plain,(
    ! [A_23,A_284] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_284)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_284)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1950])).

tff(c_3929,plain,(
    ! [A_408,A_409] :
      ( k5_relat_1(k6_relat_1(A_408),k6_relat_1(A_409)) = k6_relat_1(A_408)
      | ~ r1_tarski(A_408,A_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1959])).

tff(c_46,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3938,plain,(
    ! [A_409,A_408] :
      ( k7_relat_1(k6_relat_1(A_409),A_408) = k6_relat_1(A_408)
      | ~ v1_relat_1(k6_relat_1(A_409))
      | ~ r1_tarski(A_408,A_409) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3929,c_46])).

tff(c_3999,plain,(
    ! [A_412,A_413] :
      ( k7_relat_1(k6_relat_1(A_412),A_413) = k6_relat_1(A_413)
      | ~ r1_tarski(A_413,A_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3938])).

tff(c_4014,plain,(
    ! [A_412,A_413] :
      ( k9_relat_1(k6_relat_1(A_412),A_413) = k2_relat_1(k6_relat_1(A_413))
      | ~ v1_relat_1(k6_relat_1(A_412))
      | ~ r1_tarski(A_413,A_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3999,c_16])).

tff(c_4076,plain,(
    ! [A_416,A_417] :
      ( k9_relat_1(k6_relat_1(A_416),A_417) = A_417
      | ~ r1_tarski(A_417,A_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_4014])).

tff(c_4097,plain,(
    ! [A_417,A_30] :
      ( k9_relat_1(k1_xboole_0,A_417) = A_417
      | ~ r1_tarski(A_417,A_30)
      | k1_xboole_0 != A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4076])).

tff(c_4102,plain,(
    ! [A_418,A_419] :
      ( k1_xboole_0 = A_418
      | ~ r1_tarski(A_418,A_419)
      | k1_xboole_0 != A_419 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1847,c_4097])).

tff(c_4141,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_186,c_4102])).

tff(c_4157,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3048,c_4141])).

tff(c_11332,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11255,c_4157])).

tff(c_11677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11395,c_11332])).

tff(c_11678,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_11253])).

tff(c_11713,plain,
    ( k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11678,c_44])).

tff(c_11732,plain,(
    k5_relat_1('#skF_3',k6_relat_1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_11713])).

tff(c_2159,plain,(
    ! [A_299,B_300] :
      ( k10_relat_1(A_299,k1_relat_1(B_300)) = k1_relat_1(k5_relat_1(A_299,B_300))
      | ~ v1_relat_1(B_300)
      | ~ v1_relat_1(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2210,plain,(
    ! [A_299,A_23] :
      ( k1_relat_1(k5_relat_1(A_299,k6_relat_1(A_23))) = k10_relat_1(A_299,A_23)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2159])).

tff(c_2237,plain,(
    ! [A_299,A_23] :
      ( k1_relat_1(k5_relat_1(A_299,k6_relat_1(A_23))) = k10_relat_1(A_299,A_23)
      | ~ v1_relat_1(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2210])).

tff(c_11740,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11732,c_2237])).

tff(c_11749,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_11740])).

tff(c_11751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2407,c_11749])).

tff(c_11753,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9647])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11879,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11753,c_11753,c_8])).

tff(c_11817,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11753,c_4157])).

tff(c_12094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11879,c_11817])).

tff(c_12096,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3045])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12154,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12096,c_12096,c_34])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1524,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1516,c_38])).

tff(c_1526,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1524])).

tff(c_12143,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12096,c_1526])).

tff(c_12249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12154,c_12143])).

tff(c_12250,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1524])).

tff(c_12262,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12250,c_12250,c_32])).

tff(c_36,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1523,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1516,c_36])).

tff(c_1525,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1523])).

tff(c_12252,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12250,c_1525])).

tff(c_12289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12262,c_12252])).

tff(c_12290,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1523])).

tff(c_12303,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_34])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12317,plain,(
    ! [A_10] :
      ( r1_tarski(k10_relat_1('#skF_3',A_10),'#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12303,c_18])).

tff(c_12321,plain,(
    ! [A_10] : r1_tarski(k10_relat_1('#skF_3',A_10),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_12317])).

tff(c_1514,plain,(
    ! [C_214] :
      ( v1_relat_1(C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1503])).

tff(c_12406,plain,(
    ! [C_656] :
      ( v1_relat_1(C_656)
      | ~ m1_subset_1(C_656,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_1514])).

tff(c_12412,plain,(
    ! [A_657] :
      ( v1_relat_1(A_657)
      | ~ r1_tarski(A_657,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_12406])).

tff(c_12424,plain,(
    ! [A_10] : v1_relat_1(k10_relat_1('#skF_3',A_10)) ),
    inference(resolution,[status(thm)],[c_12321,c_12412])).

tff(c_12377,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_144])).

tff(c_12300,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_6])).

tff(c_1480,plain,(
    ! [B_207,A_208] :
      ( r1_tarski(k10_relat_1(B_207,A_208),k1_relat_1(B_207))
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1483,plain,(
    ! [A_23,A_208] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_23),A_208),A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1480])).

tff(c_1488,plain,(
    ! [A_23,A_208] : r1_tarski(k10_relat_1(k6_relat_1(A_23),A_208),A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1483])).

tff(c_12441,plain,(
    ! [C_661,A_662,B_663] :
      ( v4_relat_1(C_661,A_662)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(A_662,B_663))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_12702,plain,(
    ! [A_696,A_697,B_698] :
      ( v4_relat_1(A_696,A_697)
      | ~ r1_tarski(A_696,k2_zfmisc_1(A_697,B_698)) ) ),
    inference(resolution,[status(thm)],[c_12,c_12441])).

tff(c_12815,plain,(
    ! [A_709,B_710,A_711] : v4_relat_1(k10_relat_1(k6_relat_1(k2_zfmisc_1(A_709,B_710)),A_711),A_709) ),
    inference(resolution,[status(thm)],[c_1488,c_12702])).

tff(c_12824,plain,(
    ! [A_711,A_2] : v4_relat_1(k10_relat_1(k6_relat_1('#skF_3'),A_711),A_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_12300,c_12815])).

tff(c_12855,plain,(
    ! [A_715,A_716] : v4_relat_1(k10_relat_1('#skF_3',A_715),A_716) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12377,c_12824])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12858,plain,(
    ! [A_715,A_716] :
      ( k7_relat_1(k10_relat_1('#skF_3',A_715),A_716) = k10_relat_1('#skF_3',A_715)
      | ~ v1_relat_1(k10_relat_1('#skF_3',A_715)) ) ),
    inference(resolution,[status(thm)],[c_12855,c_26])).

tff(c_12861,plain,(
    ! [A_715,A_716] : k7_relat_1(k10_relat_1('#skF_3',A_715),A_716) = k10_relat_1('#skF_3',A_715) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12858])).

tff(c_1492,plain,(
    ! [A_210,A_211] : r1_tarski(k10_relat_1(k6_relat_1(A_210),A_211),A_210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1483])).

tff(c_1495,plain,(
    ! [A_211,A_30] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_211),A_30)
      | k1_xboole_0 != A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1492])).

tff(c_12604,plain,(
    ! [A_211] : r1_tarski(k10_relat_1('#skF_3',A_211),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_1495])).

tff(c_12882,plain,(
    ! [A_723,A_724] : k7_relat_1(k10_relat_1('#skF_3',A_723),A_724) = k10_relat_1('#skF_3',A_723) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12858])).

tff(c_12888,plain,(
    ! [A_723,A_724] :
      ( k9_relat_1(k10_relat_1('#skF_3',A_723),A_724) = k2_relat_1(k10_relat_1('#skF_3',A_723))
      | ~ v1_relat_1(k10_relat_1('#skF_3',A_723)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12882,c_16])).

tff(c_13604,plain,(
    ! [A_769,A_770] : k9_relat_1(k10_relat_1('#skF_3',A_769),A_770) = k2_relat_1(k10_relat_1('#skF_3',A_769)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12888])).

tff(c_12291,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1523])).

tff(c_12309,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12291])).

tff(c_12914,plain,(
    ! [A_727,B_728] :
      ( r1_tarski(k2_relat_1(A_727),k2_relat_1(B_728))
      | ~ r1_tarski(A_727,B_728)
      | ~ v1_relat_1(B_728)
      | ~ v1_relat_1(A_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12935,plain,(
    ! [A_727] :
      ( r1_tarski(k2_relat_1(A_727),'#skF_3')
      | ~ r1_tarski(A_727,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_727) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12309,c_12914])).

tff(c_12998,plain,(
    ! [A_735] :
      ( r1_tarski(k2_relat_1(A_735),'#skF_3')
      | ~ r1_tarski(A_735,'#skF_3')
      | ~ v1_relat_1(A_735) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_12935])).

tff(c_13010,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k9_relat_1(B_9,A_8),'#skF_3')
      | ~ r1_tarski(k7_relat_1(B_9,A_8),'#skF_3')
      | ~ v1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_12998])).

tff(c_13610,plain,(
    ! [A_769,A_770] :
      ( r1_tarski(k2_relat_1(k10_relat_1('#skF_3',A_769)),'#skF_3')
      | ~ r1_tarski(k7_relat_1(k10_relat_1('#skF_3',A_769),A_770),'#skF_3')
      | ~ v1_relat_1(k7_relat_1(k10_relat_1('#skF_3',A_769),A_770))
      | ~ v1_relat_1(k10_relat_1('#skF_3',A_769)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13604,c_13010])).

tff(c_13620,plain,(
    ! [A_769] : r1_tarski(k2_relat_1(k10_relat_1('#skF_3',A_769)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12424,c_12861,c_12604,c_12861,c_13610])).

tff(c_12302,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_2])).

tff(c_12655,plain,(
    ! [B_688,A_689] :
      ( k7_relat_1(B_688,A_689) = B_688
      | ~ r1_tarski(k1_relat_1(B_688),A_689)
      | ~ v1_relat_1(B_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12661,plain,(
    ! [A_689] :
      ( k7_relat_1('#skF_3',A_689) = '#skF_3'
      | ~ r1_tarski('#skF_3',A_689)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12303,c_12655])).

tff(c_12672,plain,(
    ! [A_690] : k7_relat_1('#skF_3',A_690) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_12302,c_12661])).

tff(c_12677,plain,(
    ! [A_690] :
      ( k9_relat_1('#skF_3',A_690) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12672,c_16])).

tff(c_12682,plain,(
    ! [A_690] : k9_relat_1('#skF_3',A_690) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_12309,c_12677])).

tff(c_12296,plain,(
    ! [A_30] :
      ( A_30 != '#skF_3'
      | k6_relat_1(A_30) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_144])).

tff(c_12724,plain,(
    ! [B_699,A_700] :
      ( k5_relat_1(B_699,k6_relat_1(A_700)) = B_699
      | ~ r1_tarski(k2_relat_1(B_699),A_700)
      | ~ v1_relat_1(B_699) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12736,plain,(
    ! [A_23,A_700] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_700)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_700)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12724])).

tff(c_14678,plain,(
    ! [A_828,A_829] :
      ( k5_relat_1(k6_relat_1(A_828),k6_relat_1(A_829)) = k6_relat_1(A_828)
      | ~ r1_tarski(A_828,A_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12736])).

tff(c_14694,plain,(
    ! [A_829,A_26] :
      ( k7_relat_1(k6_relat_1(A_829),A_26) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_829)
      | ~ v1_relat_1(k6_relat_1(A_829)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_14678])).

tff(c_14990,plain,(
    ! [A_845,A_846] :
      ( k7_relat_1(k6_relat_1(A_845),A_846) = k6_relat_1(A_846)
      | ~ r1_tarski(A_846,A_845) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14694])).

tff(c_15009,plain,(
    ! [A_845,A_846] :
      ( k9_relat_1(k6_relat_1(A_845),A_846) = k2_relat_1(k6_relat_1(A_846))
      | ~ v1_relat_1(k6_relat_1(A_845))
      | ~ r1_tarski(A_846,A_845) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14990,c_16])).

tff(c_15139,plain,(
    ! [A_848,A_849] :
      ( k9_relat_1(k6_relat_1(A_848),A_849) = A_849
      | ~ r1_tarski(A_849,A_848) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_15009])).

tff(c_15164,plain,(
    ! [A_849,A_30] :
      ( k9_relat_1('#skF_3',A_849) = A_849
      | ~ r1_tarski(A_849,A_30)
      | A_30 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12296,c_15139])).

tff(c_15175,plain,(
    ! [A_850,A_851] :
      ( A_850 = '#skF_3'
      | ~ r1_tarski(A_850,A_851)
      | A_851 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12682,c_15164])).

tff(c_15223,plain,(
    ! [A_769] : k2_relat_1(k10_relat_1('#skF_3',A_769)) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13620,c_15175])).

tff(c_12515,plain,(
    ! [A_669] :
      ( k2_relat_1(A_669) != '#skF_3'
      | A_669 = '#skF_3'
      | ~ v1_relat_1(A_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12290,c_12290,c_36])).

tff(c_12528,plain,(
    ! [A_10] :
      ( k2_relat_1(k10_relat_1('#skF_3',A_10)) != '#skF_3'
      | k10_relat_1('#skF_3',A_10) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_12424,c_12515])).

tff(c_15233,plain,(
    ! [A_10] : k10_relat_1('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15223,c_12528])).

tff(c_13624,plain,(
    ! [A_771,B_772,C_773,D_774] :
      ( k8_relset_1(A_771,B_772,C_773,D_774) = k10_relat_1(C_773,D_774)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1(A_771,B_772))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_13635,plain,(
    ! [D_774] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_774) = k10_relat_1('#skF_3',D_774) ),
    inference(resolution,[status(thm)],[c_70,c_13624])).

tff(c_13216,plain,(
    ! [A_751,B_752,C_753] :
      ( k1_relset_1(A_751,B_752,C_753) = k1_relat_1(C_753)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_13229,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_13216])).

tff(c_13232,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12303,c_13229])).

tff(c_13233,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13232,c_1445])).

tff(c_13678,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13635,c_13233])).

tff(c_15323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15233,c_13678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/3.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.08  
% 9.32/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.32/3.08  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.32/3.08  
% 9.32/3.08  %Foreground sorts:
% 9.32/3.08  
% 9.32/3.08  
% 9.32/3.08  %Background operators:
% 9.32/3.08  
% 9.32/3.08  
% 9.32/3.08  %Foreground operators:
% 9.32/3.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.32/3.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.32/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.32/3.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.32/3.08  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 9.32/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.32/3.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.32/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.32/3.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.32/3.08  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.32/3.08  tff('#skF_2', type, '#skF_2': $i).
% 9.32/3.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.32/3.08  tff('#skF_3', type, '#skF_3': $i).
% 9.32/3.08  tff('#skF_1', type, '#skF_1': $i).
% 9.32/3.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.32/3.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.32/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.32/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.32/3.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.32/3.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.32/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.32/3.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.32/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.32/3.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.32/3.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.32/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.32/3.08  
% 9.43/3.12  tff(f_151, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 9.43/3.12  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.43/3.12  tff(f_144, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 9.43/3.12  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.43/3.12  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.43/3.12  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 9.43/3.12  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.43/3.12  tff(f_140, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.43/3.12  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.43/3.12  tff(f_98, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.43/3.12  tff(f_118, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.43/3.12  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.43/3.12  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 9.43/3.12  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.43/3.12  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.43/3.12  tff(f_66, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 9.43/3.12  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.43/3.12  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.43/3.12  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.43/3.12  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.43/3.12  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 9.43/3.12  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 9.43/3.12  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 9.43/3.12  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.43/3.12  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.43/3.12  tff(c_1503, plain, (![C_214, A_215, B_216]: (v1_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.43/3.12  tff(c_1516, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1503])).
% 9.43/3.12  tff(c_2395, plain, (![A_311, B_312, C_313, D_314]: (k8_relset_1(A_311, B_312, C_313, D_314)=k10_relat_1(C_313, D_314) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.43/3.12  tff(c_2406, plain, (![D_314]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_314)=k10_relat_1('#skF_3', D_314))), inference(resolution, [status(thm)], [c_70, c_2395])).
% 9.43/3.12  tff(c_2039, plain, (![A_291, B_292, C_293]: (k1_relset_1(A_291, B_292, C_293)=k1_relat_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.43/3.12  tff(c_2054, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2039])).
% 9.43/3.12  tff(c_210, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.43/3.12  tff(c_223, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_210])).
% 9.43/3.12  tff(c_314, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.43/3.12  tff(c_329, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_314])).
% 9.43/3.12  tff(c_545, plain, (![B_131, A_132]: (k7_relat_1(B_131, A_132)=B_131 | ~v4_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.43/3.12  tff(c_560, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_545])).
% 9.43/3.12  tff(c_573, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_560])).
% 9.43/3.12  tff(c_594, plain, (![B_136, A_137]: (k2_relat_1(k7_relat_1(B_136, A_137))=k9_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.43/3.12  tff(c_609, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_573, c_594])).
% 9.43/3.12  tff(c_617, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_609])).
% 9.43/3.12  tff(c_1429, plain, (![A_198, B_199, C_200, D_201]: (k7_relset_1(A_198, B_199, C_200, D_201)=k9_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.43/3.12  tff(c_1440, plain, (![D_201]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_201)=k9_relat_1('#skF_3', D_201))), inference(resolution, [status(thm)], [c_70, c_1429])).
% 9.43/3.12  tff(c_985, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.43/3.12  tff(c_1000, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_985])).
% 9.43/3.12  tff(c_68, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.43/3.12  tff(c_187, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 9.43/3.12  tff(c_1001, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_187])).
% 9.43/3.12  tff(c_1441, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_1001])).
% 9.43/3.12  tff(c_1444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_1441])).
% 9.43/3.12  tff(c_1445, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 9.43/3.12  tff(c_2055, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2054, c_1445])).
% 9.43/3.12  tff(c_2407, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2055])).
% 9.43/3.12  tff(c_40, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.43/3.12  tff(c_50, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.43/3.12  tff(c_128, plain, (![A_60]: (k1_relat_1(A_60)!=k1_xboole_0 | k1_xboole_0=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.43/3.12  tff(c_137, plain, (![A_30]: (k1_relat_1(k6_relat_1(A_30))!=k1_xboole_0 | k6_relat_1(A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_128])).
% 9.43/3.12  tff(c_144, plain, (![A_30]: (k1_xboole_0!=A_30 | k6_relat_1(A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_137])).
% 9.43/3.12  tff(c_1730, plain, (![A_249, B_250]: (k5_relat_1(k6_relat_1(A_249), B_250)=k7_relat_1(B_250, A_249) | ~v1_relat_1(B_250))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.43/3.12  tff(c_9465, plain, (![B_588, A_589]: (k7_relat_1(B_588, A_589)=k5_relat_1(k1_xboole_0, B_588) | ~v1_relat_1(B_588) | k1_xboole_0!=A_589)), inference(superposition, [status(thm), theory('equality')], [c_144, c_1730])).
% 9.43/3.12  tff(c_9631, plain, (![A_594]: (k7_relat_1('#skF_3', A_594)=k5_relat_1(k1_xboole_0, '#skF_3') | k1_xboole_0!=A_594)), inference(resolution, [status(thm)], [c_1516, c_9465])).
% 9.43/3.12  tff(c_1527, plain, (![C_217, A_218, B_219]: (v4_relat_1(C_217, A_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.43/3.12  tff(c_1542, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_1527])).
% 9.43/3.12  tff(c_1798, plain, (![B_263, A_264]: (k7_relat_1(B_263, A_264)=B_263 | ~v4_relat_1(B_263, A_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.43/3.12  tff(c_1813, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1542, c_1798])).
% 9.43/3.12  tff(c_1826, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_1813])).
% 9.43/3.12  tff(c_9647, plain, (k5_relat_1(k1_xboole_0, '#skF_3')='#skF_3' | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9631, c_1826])).
% 9.43/3.12  tff(c_9677, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_9647])).
% 9.43/3.12  tff(c_182, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.43/3.12  tff(c_186, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_182])).
% 9.43/3.12  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.43/3.12  tff(c_22, plain, (![A_15, B_16]: (k2_relat_1(k2_zfmisc_1(A_15, B_16))=B_16 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.43/3.12  tff(c_2063, plain, (![A_294, B_295]: (r1_tarski(k2_relat_1(A_294), k2_relat_1(B_295)) | ~r1_tarski(A_294, B_295) | ~v1_relat_1(B_295) | ~v1_relat_1(A_294))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.43/3.12  tff(c_2072, plain, (![A_294, B_16, A_15]: (r1_tarski(k2_relat_1(A_294), B_16) | ~r1_tarski(A_294, k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(k2_zfmisc_1(A_15, B_16)) | ~v1_relat_1(A_294) | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(superposition, [status(thm), theory('equality')], [c_22, c_2063])).
% 9.43/3.12  tff(c_11197, plain, (![A_617, B_618, A_619]: (r1_tarski(k2_relat_1(A_617), B_618) | ~r1_tarski(A_617, k2_zfmisc_1(A_619, B_618)) | ~v1_relat_1(A_617) | k1_xboole_0=B_618 | k1_xboole_0=A_619)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2072])).
% 9.43/3.12  tff(c_11232, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_186, c_11197])).
% 9.43/3.12  tff(c_11252, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_11232])).
% 9.43/3.12  tff(c_11253, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_9677, c_11252])).
% 9.43/3.12  tff(c_11255, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_11253])).
% 9.43/3.12  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.43/3.12  tff(c_11395, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11255, c_11255, c_6])).
% 9.43/3.12  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.43/3.12  tff(c_2309, plain, (![A_306, B_307]: (r1_tarski(k1_relat_1(A_306), k1_relat_1(B_307)) | ~r1_tarski(A_306, B_307) | ~v1_relat_1(B_307) | ~v1_relat_1(A_306))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.43/3.12  tff(c_2321, plain, (![A_23, B_307]: (r1_tarski(A_23, k1_relat_1(B_307)) | ~r1_tarski(k6_relat_1(A_23), B_307) | ~v1_relat_1(B_307) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2309])).
% 9.43/3.12  tff(c_2689, plain, (![A_335, B_336]: (r1_tarski(A_335, k1_relat_1(B_336)) | ~r1_tarski(k6_relat_1(A_335), B_336) | ~v1_relat_1(B_336))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2321])).
% 9.43/3.12  tff(c_2700, plain, (![A_30, B_336]: (r1_tarski(A_30, k1_relat_1(B_336)) | ~r1_tarski(k1_xboole_0, B_336) | ~v1_relat_1(B_336) | k1_xboole_0!=A_30)), inference(superposition, [status(thm), theory('equality')], [c_144, c_2689])).
% 9.43/3.12  tff(c_2710, plain, (![A_337, B_338]: (r1_tarski(A_337, k1_relat_1(B_338)) | ~v1_relat_1(B_338) | k1_xboole_0!=A_337)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2700])).
% 9.43/3.12  tff(c_2731, plain, (![A_337, A_23]: (r1_tarski(A_337, A_23) | ~v1_relat_1(k6_relat_1(A_23)) | k1_xboole_0!=A_337)), inference(superposition, [status(thm), theory('equality')], [c_40, c_2710])).
% 9.43/3.12  tff(c_2741, plain, (![A_337, A_23]: (r1_tarski(A_337, A_23) | k1_xboole_0!=A_337)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2731])).
% 9.43/3.12  tff(c_145, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_137])).
% 9.43/3.12  tff(c_89, plain, (![A_55, B_56]: (v1_relat_1(k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.43/3.12  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_89])).
% 9.43/3.12  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.43/3.12  tff(c_2090, plain, (![A_294]: (r1_tarski(k2_relat_1(A_294), k1_xboole_0) | ~r1_tarski(A_294, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_294))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2063])).
% 9.43/3.12  tff(c_2104, plain, (![A_296]: (r1_tarski(k2_relat_1(A_296), k1_xboole_0) | ~r1_tarski(A_296, k1_xboole_0) | ~v1_relat_1(A_296))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_2090])).
% 9.43/3.12  tff(c_44, plain, (![B_25, A_24]: (k5_relat_1(B_25, k6_relat_1(A_24))=B_25 | ~r1_tarski(k2_relat_1(B_25), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.43/3.12  tff(c_2107, plain, (![A_296]: (k5_relat_1(A_296, k6_relat_1(k1_xboole_0))=A_296 | ~r1_tarski(A_296, k1_xboole_0) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_2104, c_44])).
% 9.43/3.12  tff(c_2945, plain, (![A_350]: (k5_relat_1(A_350, k1_xboole_0)=A_350 | ~r1_tarski(A_350, k1_xboole_0) | ~v1_relat_1(A_350))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2107])).
% 9.43/3.12  tff(c_3010, plain, (![A_354]: (k5_relat_1(A_354, k1_xboole_0)=A_354 | ~v1_relat_1(A_354) | k1_xboole_0!=A_354)), inference(resolution, [status(thm)], [c_2741, c_2945])).
% 9.43/3.12  tff(c_3045, plain, (k5_relat_1('#skF_3', k1_xboole_0)='#skF_3' | k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_1516, c_3010])).
% 9.43/3.12  tff(c_3048, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3045])).
% 9.43/3.12  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.43/3.12  tff(c_1660, plain, (![A_237, A_238, B_239]: (v4_relat_1(A_237, A_238) | ~r1_tarski(A_237, k2_zfmisc_1(A_238, B_239)))), inference(resolution, [status(thm)], [c_12, c_1527])).
% 9.43/3.12  tff(c_1686, plain, (![A_238]: (v4_relat_1(k1_xboole_0, A_238))), inference(resolution, [status(thm)], [c_2, c_1660])).
% 9.43/3.12  tff(c_1807, plain, (![A_238]: (k7_relat_1(k1_xboole_0, A_238)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1686, c_1798])).
% 9.43/3.12  tff(c_1837, plain, (![A_266]: (k7_relat_1(k1_xboole_0, A_266)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1807])).
% 9.43/3.12  tff(c_16, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.43/3.12  tff(c_1842, plain, (![A_266]: (k9_relat_1(k1_xboole_0, A_266)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1837, c_16])).
% 9.43/3.12  tff(c_1847, plain, (![A_266]: (k9_relat_1(k1_xboole_0, A_266)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_32, c_1842])).
% 9.43/3.12  tff(c_42, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.43/3.12  tff(c_1950, plain, (![B_283, A_284]: (k5_relat_1(B_283, k6_relat_1(A_284))=B_283 | ~r1_tarski(k2_relat_1(B_283), A_284) | ~v1_relat_1(B_283))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.43/3.12  tff(c_1959, plain, (![A_23, A_284]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_284))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_284) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1950])).
% 9.43/3.12  tff(c_3929, plain, (![A_408, A_409]: (k5_relat_1(k6_relat_1(A_408), k6_relat_1(A_409))=k6_relat_1(A_408) | ~r1_tarski(A_408, A_409))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1959])).
% 9.43/3.12  tff(c_46, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.43/3.12  tff(c_3938, plain, (![A_409, A_408]: (k7_relat_1(k6_relat_1(A_409), A_408)=k6_relat_1(A_408) | ~v1_relat_1(k6_relat_1(A_409)) | ~r1_tarski(A_408, A_409))), inference(superposition, [status(thm), theory('equality')], [c_3929, c_46])).
% 9.43/3.12  tff(c_3999, plain, (![A_412, A_413]: (k7_relat_1(k6_relat_1(A_412), A_413)=k6_relat_1(A_413) | ~r1_tarski(A_413, A_412))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3938])).
% 9.43/3.12  tff(c_4014, plain, (![A_412, A_413]: (k9_relat_1(k6_relat_1(A_412), A_413)=k2_relat_1(k6_relat_1(A_413)) | ~v1_relat_1(k6_relat_1(A_412)) | ~r1_tarski(A_413, A_412))), inference(superposition, [status(thm), theory('equality')], [c_3999, c_16])).
% 9.43/3.12  tff(c_4076, plain, (![A_416, A_417]: (k9_relat_1(k6_relat_1(A_416), A_417)=A_417 | ~r1_tarski(A_417, A_416))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_4014])).
% 9.43/3.12  tff(c_4097, plain, (![A_417, A_30]: (k9_relat_1(k1_xboole_0, A_417)=A_417 | ~r1_tarski(A_417, A_30) | k1_xboole_0!=A_30)), inference(superposition, [status(thm), theory('equality')], [c_144, c_4076])).
% 9.43/3.12  tff(c_4102, plain, (![A_418, A_419]: (k1_xboole_0=A_418 | ~r1_tarski(A_418, A_419) | k1_xboole_0!=A_419)), inference(demodulation, [status(thm), theory('equality')], [c_1847, c_4097])).
% 9.43/3.12  tff(c_4141, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_186, c_4102])).
% 9.43/3.12  tff(c_4157, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3048, c_4141])).
% 9.43/3.12  tff(c_11332, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11255, c_4157])).
% 9.43/3.12  tff(c_11677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11395, c_11332])).
% 9.43/3.12  tff(c_11678, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_11253])).
% 9.43/3.12  tff(c_11713, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11678, c_44])).
% 9.43/3.12  tff(c_11732, plain, (k5_relat_1('#skF_3', k6_relat_1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_11713])).
% 9.43/3.12  tff(c_2159, plain, (![A_299, B_300]: (k10_relat_1(A_299, k1_relat_1(B_300))=k1_relat_1(k5_relat_1(A_299, B_300)) | ~v1_relat_1(B_300) | ~v1_relat_1(A_299))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.43/3.12  tff(c_2210, plain, (![A_299, A_23]: (k1_relat_1(k5_relat_1(A_299, k6_relat_1(A_23)))=k10_relat_1(A_299, A_23) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(A_299))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2159])).
% 9.43/3.12  tff(c_2237, plain, (![A_299, A_23]: (k1_relat_1(k5_relat_1(A_299, k6_relat_1(A_23)))=k10_relat_1(A_299, A_23) | ~v1_relat_1(A_299))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2210])).
% 9.43/3.12  tff(c_11740, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11732, c_2237])).
% 9.43/3.12  tff(c_11749, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_11740])).
% 9.43/3.12  tff(c_11751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2407, c_11749])).
% 9.43/3.12  tff(c_11753, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_9647])).
% 9.43/3.12  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.43/3.12  tff(c_11879, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11753, c_11753, c_8])).
% 9.43/3.12  tff(c_11817, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11753, c_4157])).
% 9.43/3.12  tff(c_12094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11879, c_11817])).
% 9.43/3.12  tff(c_12096, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3045])).
% 9.43/3.12  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.43/3.12  tff(c_12154, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12096, c_12096, c_34])).
% 9.43/3.12  tff(c_38, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.43/3.12  tff(c_1524, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1516, c_38])).
% 9.43/3.12  tff(c_1526, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1524])).
% 9.43/3.12  tff(c_12143, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12096, c_1526])).
% 9.43/3.12  tff(c_12249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12154, c_12143])).
% 9.43/3.12  tff(c_12250, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1524])).
% 9.43/3.12  tff(c_12262, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12250, c_12250, c_32])).
% 9.43/3.12  tff(c_36, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.43/3.12  tff(c_1523, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1516, c_36])).
% 9.43/3.12  tff(c_1525, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1523])).
% 9.43/3.12  tff(c_12252, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12250, c_1525])).
% 9.43/3.12  tff(c_12289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12262, c_12252])).
% 9.43/3.12  tff(c_12290, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1523])).
% 9.43/3.12  tff(c_12303, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_34])).
% 9.43/3.12  tff(c_18, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.43/3.12  tff(c_12317, plain, (![A_10]: (r1_tarski(k10_relat_1('#skF_3', A_10), '#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12303, c_18])).
% 9.43/3.12  tff(c_12321, plain, (![A_10]: (r1_tarski(k10_relat_1('#skF_3', A_10), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_12317])).
% 9.43/3.12  tff(c_1514, plain, (![C_214]: (v1_relat_1(C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1503])).
% 9.43/3.12  tff(c_12406, plain, (![C_656]: (v1_relat_1(C_656) | ~m1_subset_1(C_656, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_1514])).
% 9.43/3.12  tff(c_12412, plain, (![A_657]: (v1_relat_1(A_657) | ~r1_tarski(A_657, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_12406])).
% 9.43/3.12  tff(c_12424, plain, (![A_10]: (v1_relat_1(k10_relat_1('#skF_3', A_10)))), inference(resolution, [status(thm)], [c_12321, c_12412])).
% 9.43/3.12  tff(c_12377, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_144])).
% 9.43/3.12  tff(c_12300, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_6])).
% 9.43/3.12  tff(c_1480, plain, (![B_207, A_208]: (r1_tarski(k10_relat_1(B_207, A_208), k1_relat_1(B_207)) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.43/3.12  tff(c_1483, plain, (![A_23, A_208]: (r1_tarski(k10_relat_1(k6_relat_1(A_23), A_208), A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1480])).
% 9.43/3.12  tff(c_1488, plain, (![A_23, A_208]: (r1_tarski(k10_relat_1(k6_relat_1(A_23), A_208), A_23))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1483])).
% 9.43/3.12  tff(c_12441, plain, (![C_661, A_662, B_663]: (v4_relat_1(C_661, A_662) | ~m1_subset_1(C_661, k1_zfmisc_1(k2_zfmisc_1(A_662, B_663))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.43/3.12  tff(c_12702, plain, (![A_696, A_697, B_698]: (v4_relat_1(A_696, A_697) | ~r1_tarski(A_696, k2_zfmisc_1(A_697, B_698)))), inference(resolution, [status(thm)], [c_12, c_12441])).
% 9.43/3.12  tff(c_12815, plain, (![A_709, B_710, A_711]: (v4_relat_1(k10_relat_1(k6_relat_1(k2_zfmisc_1(A_709, B_710)), A_711), A_709))), inference(resolution, [status(thm)], [c_1488, c_12702])).
% 9.43/3.12  tff(c_12824, plain, (![A_711, A_2]: (v4_relat_1(k10_relat_1(k6_relat_1('#skF_3'), A_711), A_2))), inference(superposition, [status(thm), theory('equality')], [c_12300, c_12815])).
% 9.43/3.12  tff(c_12855, plain, (![A_715, A_716]: (v4_relat_1(k10_relat_1('#skF_3', A_715), A_716))), inference(demodulation, [status(thm), theory('equality')], [c_12377, c_12824])).
% 9.43/3.12  tff(c_26, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.43/3.12  tff(c_12858, plain, (![A_715, A_716]: (k7_relat_1(k10_relat_1('#skF_3', A_715), A_716)=k10_relat_1('#skF_3', A_715) | ~v1_relat_1(k10_relat_1('#skF_3', A_715)))), inference(resolution, [status(thm)], [c_12855, c_26])).
% 9.43/3.12  tff(c_12861, plain, (![A_715, A_716]: (k7_relat_1(k10_relat_1('#skF_3', A_715), A_716)=k10_relat_1('#skF_3', A_715))), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12858])).
% 9.43/3.12  tff(c_1492, plain, (![A_210, A_211]: (r1_tarski(k10_relat_1(k6_relat_1(A_210), A_211), A_210))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1483])).
% 9.43/3.12  tff(c_1495, plain, (![A_211, A_30]: (r1_tarski(k10_relat_1(k1_xboole_0, A_211), A_30) | k1_xboole_0!=A_30)), inference(superposition, [status(thm), theory('equality')], [c_144, c_1492])).
% 9.43/3.12  tff(c_12604, plain, (![A_211]: (r1_tarski(k10_relat_1('#skF_3', A_211), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_1495])).
% 9.43/3.12  tff(c_12882, plain, (![A_723, A_724]: (k7_relat_1(k10_relat_1('#skF_3', A_723), A_724)=k10_relat_1('#skF_3', A_723))), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12858])).
% 9.43/3.12  tff(c_12888, plain, (![A_723, A_724]: (k9_relat_1(k10_relat_1('#skF_3', A_723), A_724)=k2_relat_1(k10_relat_1('#skF_3', A_723)) | ~v1_relat_1(k10_relat_1('#skF_3', A_723)))), inference(superposition, [status(thm), theory('equality')], [c_12882, c_16])).
% 9.43/3.12  tff(c_13604, plain, (![A_769, A_770]: (k9_relat_1(k10_relat_1('#skF_3', A_769), A_770)=k2_relat_1(k10_relat_1('#skF_3', A_769)))), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12888])).
% 9.43/3.12  tff(c_12291, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1523])).
% 9.43/3.12  tff(c_12309, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12291])).
% 9.43/3.12  tff(c_12914, plain, (![A_727, B_728]: (r1_tarski(k2_relat_1(A_727), k2_relat_1(B_728)) | ~r1_tarski(A_727, B_728) | ~v1_relat_1(B_728) | ~v1_relat_1(A_727))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.43/3.12  tff(c_12935, plain, (![A_727]: (r1_tarski(k2_relat_1(A_727), '#skF_3') | ~r1_tarski(A_727, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_727))), inference(superposition, [status(thm), theory('equality')], [c_12309, c_12914])).
% 9.43/3.12  tff(c_12998, plain, (![A_735]: (r1_tarski(k2_relat_1(A_735), '#skF_3') | ~r1_tarski(A_735, '#skF_3') | ~v1_relat_1(A_735))), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_12935])).
% 9.43/3.12  tff(c_13010, plain, (![B_9, A_8]: (r1_tarski(k9_relat_1(B_9, A_8), '#skF_3') | ~r1_tarski(k7_relat_1(B_9, A_8), '#skF_3') | ~v1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_12998])).
% 9.43/3.12  tff(c_13610, plain, (![A_769, A_770]: (r1_tarski(k2_relat_1(k10_relat_1('#skF_3', A_769)), '#skF_3') | ~r1_tarski(k7_relat_1(k10_relat_1('#skF_3', A_769), A_770), '#skF_3') | ~v1_relat_1(k7_relat_1(k10_relat_1('#skF_3', A_769), A_770)) | ~v1_relat_1(k10_relat_1('#skF_3', A_769)))), inference(superposition, [status(thm), theory('equality')], [c_13604, c_13010])).
% 9.43/3.12  tff(c_13620, plain, (![A_769]: (r1_tarski(k2_relat_1(k10_relat_1('#skF_3', A_769)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12424, c_12861, c_12604, c_12861, c_13610])).
% 9.43/3.12  tff(c_12302, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_2])).
% 9.43/3.12  tff(c_12655, plain, (![B_688, A_689]: (k7_relat_1(B_688, A_689)=B_688 | ~r1_tarski(k1_relat_1(B_688), A_689) | ~v1_relat_1(B_688))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.43/3.12  tff(c_12661, plain, (![A_689]: (k7_relat_1('#skF_3', A_689)='#skF_3' | ~r1_tarski('#skF_3', A_689) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12303, c_12655])).
% 9.43/3.12  tff(c_12672, plain, (![A_690]: (k7_relat_1('#skF_3', A_690)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_12302, c_12661])).
% 9.43/3.12  tff(c_12677, plain, (![A_690]: (k9_relat_1('#skF_3', A_690)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12672, c_16])).
% 9.43/3.12  tff(c_12682, plain, (![A_690]: (k9_relat_1('#skF_3', A_690)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_12309, c_12677])).
% 9.43/3.12  tff(c_12296, plain, (![A_30]: (A_30!='#skF_3' | k6_relat_1(A_30)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_144])).
% 9.43/3.12  tff(c_12724, plain, (![B_699, A_700]: (k5_relat_1(B_699, k6_relat_1(A_700))=B_699 | ~r1_tarski(k2_relat_1(B_699), A_700) | ~v1_relat_1(B_699))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.43/3.12  tff(c_12736, plain, (![A_23, A_700]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_700))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_700) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_12724])).
% 9.43/3.12  tff(c_14678, plain, (![A_828, A_829]: (k5_relat_1(k6_relat_1(A_828), k6_relat_1(A_829))=k6_relat_1(A_828) | ~r1_tarski(A_828, A_829))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12736])).
% 9.43/3.12  tff(c_14694, plain, (![A_829, A_26]: (k7_relat_1(k6_relat_1(A_829), A_26)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_829) | ~v1_relat_1(k6_relat_1(A_829)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_14678])).
% 9.43/3.12  tff(c_14990, plain, (![A_845, A_846]: (k7_relat_1(k6_relat_1(A_845), A_846)=k6_relat_1(A_846) | ~r1_tarski(A_846, A_845))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14694])).
% 9.43/3.12  tff(c_15009, plain, (![A_845, A_846]: (k9_relat_1(k6_relat_1(A_845), A_846)=k2_relat_1(k6_relat_1(A_846)) | ~v1_relat_1(k6_relat_1(A_845)) | ~r1_tarski(A_846, A_845))), inference(superposition, [status(thm), theory('equality')], [c_14990, c_16])).
% 9.43/3.12  tff(c_15139, plain, (![A_848, A_849]: (k9_relat_1(k6_relat_1(A_848), A_849)=A_849 | ~r1_tarski(A_849, A_848))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_15009])).
% 9.43/3.12  tff(c_15164, plain, (![A_849, A_30]: (k9_relat_1('#skF_3', A_849)=A_849 | ~r1_tarski(A_849, A_30) | A_30!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12296, c_15139])).
% 9.43/3.12  tff(c_15175, plain, (![A_850, A_851]: (A_850='#skF_3' | ~r1_tarski(A_850, A_851) | A_851!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12682, c_15164])).
% 9.43/3.12  tff(c_15223, plain, (![A_769]: (k2_relat_1(k10_relat_1('#skF_3', A_769))='#skF_3')), inference(resolution, [status(thm)], [c_13620, c_15175])).
% 9.43/3.12  tff(c_12515, plain, (![A_669]: (k2_relat_1(A_669)!='#skF_3' | A_669='#skF_3' | ~v1_relat_1(A_669))), inference(demodulation, [status(thm), theory('equality')], [c_12290, c_12290, c_36])).
% 9.43/3.12  tff(c_12528, plain, (![A_10]: (k2_relat_1(k10_relat_1('#skF_3', A_10))!='#skF_3' | k10_relat_1('#skF_3', A_10)='#skF_3')), inference(resolution, [status(thm)], [c_12424, c_12515])).
% 9.43/3.12  tff(c_15233, plain, (![A_10]: (k10_relat_1('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15223, c_12528])).
% 9.43/3.12  tff(c_13624, plain, (![A_771, B_772, C_773, D_774]: (k8_relset_1(A_771, B_772, C_773, D_774)=k10_relat_1(C_773, D_774) | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1(A_771, B_772))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 9.43/3.12  tff(c_13635, plain, (![D_774]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_774)=k10_relat_1('#skF_3', D_774))), inference(resolution, [status(thm)], [c_70, c_13624])).
% 9.43/3.12  tff(c_13216, plain, (![A_751, B_752, C_753]: (k1_relset_1(A_751, B_752, C_753)=k1_relat_1(C_753) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.43/3.12  tff(c_13229, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_13216])).
% 9.43/3.12  tff(c_13232, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12303, c_13229])).
% 9.43/3.12  tff(c_13233, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13232, c_1445])).
% 9.43/3.12  tff(c_13678, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13635, c_13233])).
% 9.43/3.12  tff(c_15323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15233, c_13678])).
% 9.43/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.43/3.12  
% 9.43/3.12  Inference rules
% 9.43/3.12  ----------------------
% 9.43/3.12  #Ref     : 2
% 9.43/3.12  #Sup     : 3437
% 9.43/3.12  #Fact    : 0
% 9.43/3.12  #Define  : 0
% 9.43/3.12  #Split   : 19
% 9.43/3.12  #Chain   : 0
% 9.43/3.12  #Close   : 0
% 9.43/3.12  
% 9.43/3.12  Ordering : KBO
% 9.43/3.12  
% 9.43/3.12  Simplification rules
% 9.43/3.12  ----------------------
% 9.43/3.12  #Subsume      : 856
% 9.43/3.12  #Demod        : 2614
% 9.43/3.12  #Tautology    : 1216
% 9.43/3.12  #SimpNegUnit  : 138
% 9.43/3.12  #BackRed      : 464
% 9.43/3.12  
% 9.43/3.12  #Partial instantiations: 0
% 9.43/3.12  #Strategies tried      : 1
% 9.43/3.12  
% 9.43/3.12  Timing (in seconds)
% 9.43/3.12  ----------------------
% 9.43/3.12  Preprocessing        : 0.34
% 9.43/3.12  Parsing              : 0.19
% 9.43/3.12  CNF conversion       : 0.02
% 9.43/3.12  Main loop            : 2.02
% 9.43/3.12  Inferencing          : 0.58
% 9.43/3.12  Reduction            : 0.75
% 9.43/3.12  Demodulation         : 0.55
% 9.43/3.12  BG Simplification    : 0.07
% 9.43/3.12  Subsumption          : 0.46
% 9.43/3.12  Abstraction          : 0.09
% 9.43/3.12  MUC search           : 0.00
% 9.43/3.12  Cooper               : 0.00
% 9.43/3.12  Total                : 2.44
% 9.43/3.12  Index Insertion      : 0.00
% 9.43/3.12  Index Deletion       : 0.00
% 9.43/3.12  Index Matching       : 0.00
% 9.43/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
