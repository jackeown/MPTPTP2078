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
% DateTime   : Thu Dec  3 10:14:51 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 261 expanded)
%              Number of leaves         :   44 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 550 expanded)
%              Number of equality atoms :   90 ( 200 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_240,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_253,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_240])).

tff(c_38,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_262,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_253,c_50])).

tff(c_264,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_472,plain,(
    ! [B_133,A_134] :
      ( k1_tarski(k1_funct_1(B_133,A_134)) = k2_relat_1(B_133)
      | k1_tarski(A_134) != k1_relat_1(B_133)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_481,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_62])).

tff(c_505,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_70,c_481])).

tff(c_510,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_322,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_335,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_322])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_546,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k1_enumset1(A_154,B_155,C_156) = D_157
      | k2_tarski(A_154,C_156) = D_157
      | k2_tarski(B_155,C_156) = D_157
      | k2_tarski(A_154,B_155) = D_157
      | k1_tarski(C_156) = D_157
      | k1_tarski(B_155) = D_157
      | k1_tarski(A_154) = D_157
      | k1_xboole_0 = D_157
      | ~ r1_tarski(D_157,k1_enumset1(A_154,B_155,C_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_575,plain,(
    ! [A_2,B_3,D_157] :
      ( k1_enumset1(A_2,A_2,B_3) = D_157
      | k2_tarski(A_2,B_3) = D_157
      | k2_tarski(A_2,B_3) = D_157
      | k2_tarski(A_2,A_2) = D_157
      | k1_tarski(B_3) = D_157
      | k1_tarski(A_2) = D_157
      | k1_tarski(A_2) = D_157
      | k1_xboole_0 = D_157
      | ~ r1_tarski(D_157,k2_tarski(A_2,B_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_546])).

tff(c_771,plain,(
    ! [A_198,B_199,D_200] :
      ( k2_tarski(A_198,B_199) = D_200
      | k2_tarski(A_198,B_199) = D_200
      | k2_tarski(A_198,B_199) = D_200
      | k1_tarski(A_198) = D_200
      | k1_tarski(B_199) = D_200
      | k1_tarski(A_198) = D_200
      | k1_tarski(A_198) = D_200
      | k1_xboole_0 = D_200
      | ~ r1_tarski(D_200,k2_tarski(A_198,B_199)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_575])).

tff(c_810,plain,(
    ! [A_201,B_202,B_203] :
      ( k2_tarski(A_201,B_202) = k1_relat_1(B_203)
      | k1_tarski(B_202) = k1_relat_1(B_203)
      | k1_tarski(A_201) = k1_relat_1(B_203)
      | k1_relat_1(B_203) = k1_xboole_0
      | ~ v4_relat_1(B_203,k2_tarski(A_201,B_202))
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_36,c_771])).

tff(c_817,plain,(
    ! [A_1,B_203] :
      ( k2_tarski(A_1,A_1) = k1_relat_1(B_203)
      | k1_tarski(A_1) = k1_relat_1(B_203)
      | k1_tarski(A_1) = k1_relat_1(B_203)
      | k1_relat_1(B_203) = k1_xboole_0
      | ~ v4_relat_1(B_203,k1_tarski(A_1))
      | ~ v1_relat_1(B_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_810])).

tff(c_822,plain,(
    ! [A_204,B_205] :
      ( k1_tarski(A_204) = k1_relat_1(B_205)
      | k1_tarski(A_204) = k1_relat_1(B_205)
      | k1_tarski(A_204) = k1_relat_1(B_205)
      | k1_relat_1(B_205) = k1_xboole_0
      | ~ v4_relat_1(B_205,k1_tarski(A_204))
      | ~ v1_relat_1(B_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_817])).

tff(c_828,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_335,c_822])).

tff(c_835,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_828])).

tff(c_837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_510,c_835])).

tff(c_839,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_846,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_66])).

tff(c_60,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k7_relset_1(A_34,B_35,C_36,D_37) = k9_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_951,plain,(
    ! [D_37] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_37) = k9_relat_1('#skF_4',D_37) ),
    inference(resolution,[status(thm)],[c_846,c_60])).

tff(c_838,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_1190,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_838])).

tff(c_1409,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_1190])).

tff(c_1427,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1409])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_1427])).

tff(c_1432,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_26,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_1436,plain,(
    ! [A_11] : r1_tarski('#skF_4',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_138])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1440,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_1432,c_44])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1441,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_1432,c_46])).

tff(c_1548,plain,(
    ! [B_275,A_276] :
      ( v4_relat_1(B_275,A_276)
      | ~ r1_tarski(k1_relat_1(B_275),A_276)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1554,plain,(
    ! [A_276] :
      ( v4_relat_1('#skF_4',A_276)
      | ~ r1_tarski('#skF_4',A_276)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1441,c_1548])).

tff(c_1557,plain,(
    ! [A_276] : v4_relat_1('#skF_4',A_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_1436,c_1554])).

tff(c_1601,plain,(
    ! [B_289,A_290] :
      ( k7_relat_1(B_289,A_290) = B_289
      | ~ v4_relat_1(B_289,A_290)
      | ~ v1_relat_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1604,plain,(
    ! [A_276] :
      ( k7_relat_1('#skF_4',A_276) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1557,c_1601])).

tff(c_1608,plain,(
    ! [A_291] : k7_relat_1('#skF_4',A_291) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_1604])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1613,plain,(
    ! [A_291] :
      ( k9_relat_1('#skF_4',A_291) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1608,c_40])).

tff(c_1618,plain,(
    ! [A_291] : k9_relat_1('#skF_4',A_291) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_1440,c_1613])).

tff(c_1439,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_26])).

tff(c_1713,plain,(
    ! [A_315,B_316,C_317,D_318] :
      ( k7_relset_1(A_315,B_316,C_317,D_318) = k9_relat_1(C_317,D_318)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1716,plain,(
    ! [A_315,B_316,D_318] : k7_relset_1(A_315,B_316,'#skF_4',D_318) = k9_relat_1('#skF_4',D_318) ),
    inference(resolution,[status(thm)],[c_1439,c_1713])).

tff(c_1721,plain,(
    ! [A_315,B_316,D_318] : k7_relset_1(A_315,B_316,'#skF_4',D_318) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1716])).

tff(c_1775,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_62])).

tff(c_1778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_1775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  
% 3.86/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.86/1.61  
% 3.86/1.61  %Foreground sorts:
% 3.86/1.61  
% 3.86/1.61  
% 3.86/1.61  %Background operators:
% 3.86/1.61  
% 3.86/1.61  
% 3.86/1.61  %Foreground operators:
% 3.86/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.86/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.86/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.86/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.86/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.86/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.86/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.86/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.86/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.86/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.86/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.61  
% 3.86/1.63  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.86/1.63  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.86/1.63  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.86/1.63  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.86/1.63  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.86/1.63  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.86/1.63  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.86/1.63  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.86/1.63  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.86/1.63  tff(f_58, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.86/1.63  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.86/1.63  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.86/1.63  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.86/1.63  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.86/1.63  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.86/1.63  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.86/1.63  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.86/1.63  tff(c_240, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.63  tff(c_253, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_240])).
% 3.86/1.63  tff(c_38, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.63  tff(c_50, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.86/1.63  tff(c_262, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_253, c_50])).
% 3.86/1.63  tff(c_264, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_262])).
% 3.86/1.63  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.86/1.63  tff(c_472, plain, (![B_133, A_134]: (k1_tarski(k1_funct_1(B_133, A_134))=k2_relat_1(B_133) | k1_tarski(A_134)!=k1_relat_1(B_133) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.86/1.63  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.86/1.63  tff(c_481, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_472, c_62])).
% 3.86/1.63  tff(c_505, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_70, c_481])).
% 3.86/1.63  tff(c_510, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_505])).
% 3.86/1.63  tff(c_322, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.86/1.63  tff(c_335, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_322])).
% 3.86/1.63  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.86/1.63  tff(c_36, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.63  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.63  tff(c_546, plain, (![A_154, B_155, C_156, D_157]: (k1_enumset1(A_154, B_155, C_156)=D_157 | k2_tarski(A_154, C_156)=D_157 | k2_tarski(B_155, C_156)=D_157 | k2_tarski(A_154, B_155)=D_157 | k1_tarski(C_156)=D_157 | k1_tarski(B_155)=D_157 | k1_tarski(A_154)=D_157 | k1_xboole_0=D_157 | ~r1_tarski(D_157, k1_enumset1(A_154, B_155, C_156)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.86/1.63  tff(c_575, plain, (![A_2, B_3, D_157]: (k1_enumset1(A_2, A_2, B_3)=D_157 | k2_tarski(A_2, B_3)=D_157 | k2_tarski(A_2, B_3)=D_157 | k2_tarski(A_2, A_2)=D_157 | k1_tarski(B_3)=D_157 | k1_tarski(A_2)=D_157 | k1_tarski(A_2)=D_157 | k1_xboole_0=D_157 | ~r1_tarski(D_157, k2_tarski(A_2, B_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_546])).
% 3.86/1.63  tff(c_771, plain, (![A_198, B_199, D_200]: (k2_tarski(A_198, B_199)=D_200 | k2_tarski(A_198, B_199)=D_200 | k2_tarski(A_198, B_199)=D_200 | k1_tarski(A_198)=D_200 | k1_tarski(B_199)=D_200 | k1_tarski(A_198)=D_200 | k1_tarski(A_198)=D_200 | k1_xboole_0=D_200 | ~r1_tarski(D_200, k2_tarski(A_198, B_199)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_575])).
% 3.86/1.63  tff(c_810, plain, (![A_201, B_202, B_203]: (k2_tarski(A_201, B_202)=k1_relat_1(B_203) | k1_tarski(B_202)=k1_relat_1(B_203) | k1_tarski(A_201)=k1_relat_1(B_203) | k1_relat_1(B_203)=k1_xboole_0 | ~v4_relat_1(B_203, k2_tarski(A_201, B_202)) | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_36, c_771])).
% 3.86/1.63  tff(c_817, plain, (![A_1, B_203]: (k2_tarski(A_1, A_1)=k1_relat_1(B_203) | k1_tarski(A_1)=k1_relat_1(B_203) | k1_tarski(A_1)=k1_relat_1(B_203) | k1_relat_1(B_203)=k1_xboole_0 | ~v4_relat_1(B_203, k1_tarski(A_1)) | ~v1_relat_1(B_203))), inference(superposition, [status(thm), theory('equality')], [c_2, c_810])).
% 3.86/1.63  tff(c_822, plain, (![A_204, B_205]: (k1_tarski(A_204)=k1_relat_1(B_205) | k1_tarski(A_204)=k1_relat_1(B_205) | k1_tarski(A_204)=k1_relat_1(B_205) | k1_relat_1(B_205)=k1_xboole_0 | ~v4_relat_1(B_205, k1_tarski(A_204)) | ~v1_relat_1(B_205))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_817])).
% 3.86/1.63  tff(c_828, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_335, c_822])).
% 3.86/1.63  tff(c_835, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_253, c_828])).
% 3.86/1.63  tff(c_837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_510, c_835])).
% 3.86/1.63  tff(c_839, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_505])).
% 3.86/1.63  tff(c_846, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_839, c_66])).
% 3.86/1.63  tff(c_60, plain, (![A_34, B_35, C_36, D_37]: (k7_relset_1(A_34, B_35, C_36, D_37)=k9_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.63  tff(c_951, plain, (![D_37]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_37)=k9_relat_1('#skF_4', D_37))), inference(resolution, [status(thm)], [c_846, c_60])).
% 3.86/1.63  tff(c_838, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_505])).
% 3.86/1.63  tff(c_1190, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_839, c_838])).
% 3.86/1.63  tff(c_1409, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_951, c_1190])).
% 3.86/1.63  tff(c_1427, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1409])).
% 3.86/1.63  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_1427])).
% 3.86/1.63  tff(c_1432, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_262])).
% 3.86/1.63  tff(c_26, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.63  tff(c_126, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.86/1.63  tff(c_138, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_26, c_126])).
% 3.86/1.63  tff(c_1436, plain, (![A_11]: (r1_tarski('#skF_4', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_138])).
% 3.86/1.63  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.86/1.63  tff(c_1440, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_1432, c_44])).
% 3.86/1.63  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.86/1.63  tff(c_1441, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_1432, c_46])).
% 3.86/1.63  tff(c_1548, plain, (![B_275, A_276]: (v4_relat_1(B_275, A_276) | ~r1_tarski(k1_relat_1(B_275), A_276) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.86/1.63  tff(c_1554, plain, (![A_276]: (v4_relat_1('#skF_4', A_276) | ~r1_tarski('#skF_4', A_276) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1441, c_1548])).
% 3.86/1.63  tff(c_1557, plain, (![A_276]: (v4_relat_1('#skF_4', A_276))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_1436, c_1554])).
% 3.86/1.63  tff(c_1601, plain, (![B_289, A_290]: (k7_relat_1(B_289, A_290)=B_289 | ~v4_relat_1(B_289, A_290) | ~v1_relat_1(B_289))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.86/1.63  tff(c_1604, plain, (![A_276]: (k7_relat_1('#skF_4', A_276)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1557, c_1601])).
% 3.86/1.63  tff(c_1608, plain, (![A_291]: (k7_relat_1('#skF_4', A_291)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_1604])).
% 3.86/1.63  tff(c_40, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.63  tff(c_1613, plain, (![A_291]: (k9_relat_1('#skF_4', A_291)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1608, c_40])).
% 3.86/1.63  tff(c_1618, plain, (![A_291]: (k9_relat_1('#skF_4', A_291)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_1440, c_1613])).
% 3.86/1.63  tff(c_1439, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_26])).
% 3.86/1.63  tff(c_1713, plain, (![A_315, B_316, C_317, D_318]: (k7_relset_1(A_315, B_316, C_317, D_318)=k9_relat_1(C_317, D_318) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.63  tff(c_1716, plain, (![A_315, B_316, D_318]: (k7_relset_1(A_315, B_316, '#skF_4', D_318)=k9_relat_1('#skF_4', D_318))), inference(resolution, [status(thm)], [c_1439, c_1713])).
% 3.86/1.63  tff(c_1721, plain, (![A_315, B_316, D_318]: (k7_relset_1(A_315, B_316, '#skF_4', D_318)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1716])).
% 3.86/1.63  tff(c_1775, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_62])).
% 3.86/1.63  tff(c_1778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1436, c_1775])).
% 3.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.63  
% 3.86/1.63  Inference rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Ref     : 0
% 3.86/1.63  #Sup     : 357
% 3.86/1.63  #Fact    : 0
% 3.86/1.63  #Define  : 0
% 3.86/1.63  #Split   : 6
% 3.86/1.63  #Chain   : 0
% 3.86/1.63  #Close   : 0
% 3.86/1.63  
% 3.86/1.63  Ordering : KBO
% 3.86/1.63  
% 3.86/1.63  Simplification rules
% 3.86/1.63  ----------------------
% 3.86/1.63  #Subsume      : 17
% 3.86/1.63  #Demod        : 291
% 3.86/1.63  #Tautology    : 229
% 3.86/1.63  #SimpNegUnit  : 5
% 3.86/1.63  #BackRed      : 23
% 3.86/1.63  
% 3.86/1.63  #Partial instantiations: 0
% 3.86/1.63  #Strategies tried      : 1
% 3.86/1.63  
% 3.86/1.63  Timing (in seconds)
% 3.86/1.63  ----------------------
% 3.86/1.63  Preprocessing        : 0.32
% 3.86/1.63  Parsing              : 0.17
% 3.86/1.63  CNF conversion       : 0.02
% 3.86/1.63  Main loop            : 0.54
% 3.86/1.63  Inferencing          : 0.20
% 3.86/1.63  Reduction            : 0.19
% 3.86/1.63  Demodulation         : 0.14
% 3.86/1.63  BG Simplification    : 0.03
% 3.86/1.63  Subsumption          : 0.08
% 3.86/1.63  Abstraction          : 0.02
% 3.86/1.63  MUC search           : 0.00
% 3.86/1.63  Cooper               : 0.00
% 3.86/1.63  Total                : 0.90
% 3.86/1.63  Index Insertion      : 0.00
% 3.86/1.63  Index Deletion       : 0.00
% 3.86/1.63  Index Matching       : 0.00
% 3.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
