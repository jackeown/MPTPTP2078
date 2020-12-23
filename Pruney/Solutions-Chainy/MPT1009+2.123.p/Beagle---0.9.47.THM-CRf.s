%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:59 EST 2020

% Result     : Theorem 4.75s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 461 expanded)
%              Number of leaves         :   45 ( 174 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 ( 956 expanded)
%              Number of equality atoms :   54 ( 200 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_46,plain,(
    ! [A_43,B_44] : v1_relat_1(k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_139,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_142,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_142])).

tff(c_48,plain,(
    ! [B_46,A_45] :
      ( r1_tarski(k9_relat_1(B_46,A_45),k2_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_229,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_245,plain,(
    ! [C_91,A_92] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_229])).

tff(c_249,plain,(
    ! [A_36,A_92] :
      ( v4_relat_1(A_36,A_92)
      | ~ r1_tarski(A_36,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_245])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_relat_1(B_42),A_41)
      | ~ v4_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [B_35] : k2_zfmisc_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_643,plain,(
    ! [D_168,B_169,C_170,A_171] :
      ( m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(B_169,C_170)))
      | ~ r1_tarski(k1_relat_1(D_168),B_169)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(A_171,C_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_724,plain,(
    ! [B_178] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_178,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_178) ) ),
    inference(resolution,[status(thm)],[c_66,c_643])).

tff(c_744,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_724])).

tff(c_772,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_775,plain,
    ( ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_772])).

tff(c_778,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_775])).

tff(c_782,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_249,c_778])).

tff(c_90,plain,(
    ! [A_65,B_66] : v1_relat_1(k2_zfmisc_1(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [A_95,A_96,B_97] :
      ( v4_relat_1(A_95,A_96)
      | ~ r1_tarski(A_95,k2_zfmisc_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_277,plain,(
    ! [A_96,B_97] : v4_relat_1(k2_zfmisc_1(A_96,B_97),A_96) ),
    inference(resolution,[status(thm)],[c_6,c_252])).

tff(c_216,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(k1_relat_1(B_86),A_87)
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_177,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_307,plain,(
    ! [B_103] :
      ( k1_relat_1(B_103) = k1_xboole_0
      | ~ v4_relat_1(B_103,k1_xboole_0)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_216,c_189])).

tff(c_311,plain,(
    ! [B_97] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_97)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_97)) ) ),
    inference(resolution,[status(thm)],[c_277,c_307])).

tff(c_322,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_34,c_34,c_311])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_549,plain,(
    ! [B_147,A_148] :
      ( k1_tarski(k1_funct_1(B_147,A_148)) = k2_relat_1(B_147)
      | k1_tarski(A_148) != k1_relat_1(B_147)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_510,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k7_relset_1(A_141,B_142,C_143,D_144) = k9_relat_1(C_143,D_144)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_520,plain,(
    ! [D_144] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_144) = k9_relat_1('#skF_4',D_144) ),
    inference(resolution,[status(thm)],[c_66,c_510])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_522,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_62])).

tff(c_555,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_522])).

tff(c_564,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_70,c_555])).

tff(c_566,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_243,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_229])).

tff(c_289,plain,(
    ! [B_101,A_102] :
      ( k1_tarski(B_101) = A_102
      | k1_xboole_0 = A_102
      | ~ r1_tarski(A_102,k1_tarski(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2666,plain,(
    ! [B_306,B_307] :
      ( k1_tarski(B_306) = k1_relat_1(B_307)
      | k1_relat_1(B_307) = k1_xboole_0
      | ~ v4_relat_1(B_307,k1_tarski(B_306))
      | ~ v1_relat_1(B_307) ) ),
    inference(resolution,[status(thm)],[c_44,c_289])).

tff(c_2696,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_2666])).

tff(c_2709,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2696])).

tff(c_2710,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_2709])).

tff(c_2455,plain,(
    ! [B_304,B_305] :
      ( k1_tarski(B_304) = k1_relat_1(B_305)
      | k1_relat_1(B_305) = k1_xboole_0
      | ~ v4_relat_1(B_305,k1_tarski(B_304))
      | ~ v1_relat_1(B_305) ) ),
    inference(resolution,[status(thm)],[c_44,c_289])).

tff(c_2485,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_2455])).

tff(c_2498,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2485])).

tff(c_2499,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_2498])).

tff(c_1180,plain,(
    ! [B_231,B_232] :
      ( k1_tarski(B_231) = k1_relat_1(B_232)
      | k1_relat_1(B_232) = k1_xboole_0
      | ~ v4_relat_1(B_232,k1_tarski(B_231))
      | ~ v1_relat_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_44,c_289])).

tff(c_1210,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_1180])).

tff(c_1223,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1210])).

tff(c_1224,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_1223])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_792,plain,(
    ! [B_187] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_187,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_187) ) ),
    inference(resolution,[status(thm)],[c_724,c_36])).

tff(c_804,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_792])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_820,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_804,c_2])).

tff(c_909,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_1225,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_909])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34,c_1225])).

tff(c_1238,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_60,plain,(
    ! [D_60,B_58,C_59,A_57] :
      ( m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(B_58,C_59)))
      | ~ r1_tarski(k1_relat_1(D_60),B_58)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,C_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1585,plain,(
    ! [D_267,B_268] :
      ( m1_subset_1(D_267,k1_zfmisc_1(k2_zfmisc_1(B_268,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(D_267),B_268)
      | ~ m1_subset_1(D_267,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_60])).

tff(c_2338,plain,(
    ! [D_301,B_302] :
      ( r1_tarski(D_301,k2_zfmisc_1(B_302,'#skF_2'))
      | ~ r1_tarski(k1_relat_1(D_301),B_302)
      | ~ m1_subset_1(D_301,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1585,c_36])).

tff(c_2368,plain,(
    ! [D_303] :
      ( r1_tarski(D_303,k2_zfmisc_1(k1_relat_1(D_303),'#skF_2'))
      | ~ m1_subset_1(D_303,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2338])).

tff(c_56,plain,(
    ! [C_52,A_50,B_51] :
      ( v4_relat_1(C_52,A_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_749,plain,(
    ! [B_178] :
      ( v4_relat_1('#skF_4',B_178)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_178) ) ),
    inference(resolution,[status(thm)],[c_724,c_56])).

tff(c_2425,plain,
    ( v4_relat_1('#skF_4',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')),'#skF_2'))
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2368,c_749])).

tff(c_2440,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2425])).

tff(c_2444,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2440])).

tff(c_2500,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_2444])).

tff(c_2520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2500])).

tff(c_2522,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2425])).

tff(c_753,plain,(
    ! [B_178] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_178,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_178) ) ),
    inference(resolution,[status(thm)],[c_724,c_36])).

tff(c_2424,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')),'#skF_2'),'#skF_2'))
    | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2368,c_753])).

tff(c_2573,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')),'#skF_2'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_2424])).

tff(c_2713,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_2'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_2573])).

tff(c_2734,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_322,c_2713])).

tff(c_2736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_2734])).

tff(c_2737,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_2754,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2737,c_36])).

tff(c_2812,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2754,c_189])).

tff(c_2841,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2812,c_8])).

tff(c_50,plain,(
    ! [A_47] : k9_relat_1(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2839,plain,(
    ! [A_47] : k9_relat_1('#skF_4',A_47) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2812,c_2812,c_50])).

tff(c_2950,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_522])).

tff(c_2954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_2950])).

tff(c_2955,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_3005,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2955])).

tff(c_3009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.75/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.84  
% 4.75/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.75/1.84  
% 4.75/1.84  %Foreground sorts:
% 4.75/1.84  
% 4.75/1.84  
% 4.75/1.84  %Background operators:
% 4.75/1.84  
% 4.75/1.84  
% 4.75/1.84  %Foreground operators:
% 4.75/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.75/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.75/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.75/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.75/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.75/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.75/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.75/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.75/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.75/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.75/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.75/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.75/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.75/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.75/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.75/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.75/1.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.75/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.75/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.75/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.75/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.75/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.75/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.75/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.75/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.75/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.75/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.75/1.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.75/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.75/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.75/1.84  
% 4.75/1.86  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.75/1.86  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.75/1.86  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.75/1.86  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.75/1.86  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.75/1.86  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.75/1.86  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.75/1.86  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.75/1.86  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.75/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.75/1.86  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.75/1.86  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.75/1.86  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.75/1.86  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.75/1.86  tff(f_84, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 4.75/1.86  tff(c_46, plain, (![A_43, B_44]: (v1_relat_1(k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.75/1.86  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.75/1.86  tff(c_139, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.75/1.86  tff(c_142, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_139])).
% 4.75/1.86  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_142])).
% 4.75/1.86  tff(c_48, plain, (![B_46, A_45]: (r1_tarski(k9_relat_1(B_46, A_45), k2_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.75/1.86  tff(c_38, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.86  tff(c_32, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.75/1.86  tff(c_229, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.75/1.86  tff(c_245, plain, (![C_91, A_92]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_229])).
% 4.75/1.86  tff(c_249, plain, (![A_36, A_92]: (v4_relat_1(A_36, A_92) | ~r1_tarski(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_245])).
% 4.75/1.86  tff(c_44, plain, (![B_42, A_41]: (r1_tarski(k1_relat_1(B_42), A_41) | ~v4_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.86  tff(c_34, plain, (![B_35]: (k2_zfmisc_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.75/1.86  tff(c_643, plain, (![D_168, B_169, C_170, A_171]: (m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(B_169, C_170))) | ~r1_tarski(k1_relat_1(D_168), B_169) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(A_171, C_170))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.75/1.86  tff(c_724, plain, (![B_178]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_178, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_178))), inference(resolution, [status(thm)], [c_66, c_643])).
% 4.75/1.86  tff(c_744, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_724])).
% 4.75/1.86  tff(c_772, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_744])).
% 4.75/1.86  tff(c_775, plain, (~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_772])).
% 4.75/1.86  tff(c_778, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_775])).
% 4.75/1.86  tff(c_782, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_249, c_778])).
% 4.75/1.86  tff(c_90, plain, (![A_65, B_66]: (v1_relat_1(k2_zfmisc_1(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.75/1.86  tff(c_92, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_90])).
% 4.75/1.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.86  tff(c_252, plain, (![A_95, A_96, B_97]: (v4_relat_1(A_95, A_96) | ~r1_tarski(A_95, k2_zfmisc_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_38, c_229])).
% 4.75/1.86  tff(c_277, plain, (![A_96, B_97]: (v4_relat_1(k2_zfmisc_1(A_96, B_97), A_96))), inference(resolution, [status(thm)], [c_6, c_252])).
% 4.75/1.86  tff(c_216, plain, (![B_86, A_87]: (r1_tarski(k1_relat_1(B_86), A_87) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.75/1.86  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.86  tff(c_177, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.86  tff(c_189, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_177])).
% 4.75/1.86  tff(c_307, plain, (![B_103]: (k1_relat_1(B_103)=k1_xboole_0 | ~v4_relat_1(B_103, k1_xboole_0) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_216, c_189])).
% 4.75/1.86  tff(c_311, plain, (![B_97]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_97))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_97)))), inference(resolution, [status(thm)], [c_277, c_307])).
% 4.75/1.86  tff(c_322, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_34, c_34, c_311])).
% 4.75/1.86  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.75/1.86  tff(c_549, plain, (![B_147, A_148]: (k1_tarski(k1_funct_1(B_147, A_148))=k2_relat_1(B_147) | k1_tarski(A_148)!=k1_relat_1(B_147) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.75/1.86  tff(c_510, plain, (![A_141, B_142, C_143, D_144]: (k7_relset_1(A_141, B_142, C_143, D_144)=k9_relat_1(C_143, D_144) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.75/1.86  tff(c_520, plain, (![D_144]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_144)=k9_relat_1('#skF_4', D_144))), inference(resolution, [status(thm)], [c_66, c_510])).
% 4.75/1.86  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.75/1.86  tff(c_522, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_62])).
% 4.75/1.86  tff(c_555, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_549, c_522])).
% 4.75/1.86  tff(c_564, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_70, c_555])).
% 4.75/1.86  tff(c_566, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_564])).
% 4.75/1.86  tff(c_243, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_229])).
% 4.75/1.86  tff(c_289, plain, (![B_101, A_102]: (k1_tarski(B_101)=A_102 | k1_xboole_0=A_102 | ~r1_tarski(A_102, k1_tarski(B_101)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.75/1.86  tff(c_2666, plain, (![B_306, B_307]: (k1_tarski(B_306)=k1_relat_1(B_307) | k1_relat_1(B_307)=k1_xboole_0 | ~v4_relat_1(B_307, k1_tarski(B_306)) | ~v1_relat_1(B_307))), inference(resolution, [status(thm)], [c_44, c_289])).
% 4.75/1.86  tff(c_2696, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_243, c_2666])).
% 4.75/1.86  tff(c_2709, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2696])).
% 4.75/1.86  tff(c_2710, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_566, c_2709])).
% 4.75/1.86  tff(c_2455, plain, (![B_304, B_305]: (k1_tarski(B_304)=k1_relat_1(B_305) | k1_relat_1(B_305)=k1_xboole_0 | ~v4_relat_1(B_305, k1_tarski(B_304)) | ~v1_relat_1(B_305))), inference(resolution, [status(thm)], [c_44, c_289])).
% 4.75/1.86  tff(c_2485, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_243, c_2455])).
% 4.75/1.86  tff(c_2498, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2485])).
% 4.75/1.86  tff(c_2499, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_566, c_2498])).
% 4.75/1.86  tff(c_1180, plain, (![B_231, B_232]: (k1_tarski(B_231)=k1_relat_1(B_232) | k1_relat_1(B_232)=k1_xboole_0 | ~v4_relat_1(B_232, k1_tarski(B_231)) | ~v1_relat_1(B_232))), inference(resolution, [status(thm)], [c_44, c_289])).
% 4.75/1.86  tff(c_1210, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_243, c_1180])).
% 4.75/1.86  tff(c_1223, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1210])).
% 4.75/1.86  tff(c_1224, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_566, c_1223])).
% 4.75/1.86  tff(c_36, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.86  tff(c_792, plain, (![B_187]: (r1_tarski('#skF_4', k2_zfmisc_1(B_187, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_187))), inference(resolution, [status(thm)], [c_724, c_36])).
% 4.75/1.86  tff(c_804, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_792])).
% 4.75/1.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.86  tff(c_820, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_804, c_2])).
% 4.75/1.86  tff(c_909, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_820])).
% 4.75/1.86  tff(c_1225, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_909])).
% 4.75/1.86  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_34, c_1225])).
% 4.75/1.86  tff(c_1238, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_820])).
% 4.75/1.86  tff(c_60, plain, (![D_60, B_58, C_59, A_57]: (m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(B_58, C_59))) | ~r1_tarski(k1_relat_1(D_60), B_58) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_57, C_59))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.75/1.86  tff(c_1585, plain, (![D_267, B_268]: (m1_subset_1(D_267, k1_zfmisc_1(k2_zfmisc_1(B_268, '#skF_2'))) | ~r1_tarski(k1_relat_1(D_267), B_268) | ~m1_subset_1(D_267, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_60])).
% 4.75/1.86  tff(c_2338, plain, (![D_301, B_302]: (r1_tarski(D_301, k2_zfmisc_1(B_302, '#skF_2')) | ~r1_tarski(k1_relat_1(D_301), B_302) | ~m1_subset_1(D_301, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_1585, c_36])).
% 4.75/1.86  tff(c_2368, plain, (![D_303]: (r1_tarski(D_303, k2_zfmisc_1(k1_relat_1(D_303), '#skF_2')) | ~m1_subset_1(D_303, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_2338])).
% 4.75/1.86  tff(c_56, plain, (![C_52, A_50, B_51]: (v4_relat_1(C_52, A_50) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.75/1.86  tff(c_749, plain, (![B_178]: (v4_relat_1('#skF_4', B_178) | ~r1_tarski(k1_relat_1('#skF_4'), B_178))), inference(resolution, [status(thm)], [c_724, c_56])).
% 4.75/1.86  tff(c_2425, plain, (v4_relat_1('#skF_4', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')), '#skF_2')) | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_2368, c_749])).
% 4.75/1.86  tff(c_2440, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2425])).
% 4.75/1.86  tff(c_2444, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_38, c_2440])).
% 4.75/1.86  tff(c_2500, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2499, c_2444])).
% 4.75/1.86  tff(c_2520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2500])).
% 4.75/1.86  tff(c_2522, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2425])).
% 4.75/1.86  tff(c_753, plain, (![B_178]: (r1_tarski('#skF_4', k2_zfmisc_1(B_178, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_178))), inference(resolution, [status(thm)], [c_724, c_36])).
% 4.75/1.86  tff(c_2424, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')), '#skF_2'), '#skF_2')) | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_2368, c_753])).
% 4.75/1.86  tff(c_2573, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')), '#skF_2'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_2424])).
% 4.75/1.86  tff(c_2713, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_2'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_2573])).
% 4.75/1.86  tff(c_2734, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_322, c_2713])).
% 4.75/1.86  tff(c_2736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_782, c_2734])).
% 4.75/1.86  tff(c_2737, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_744])).
% 4.75/1.86  tff(c_2754, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_2737, c_36])).
% 4.75/1.86  tff(c_2812, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2754, c_189])).
% 4.75/1.86  tff(c_2841, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2812, c_8])).
% 4.75/1.86  tff(c_50, plain, (![A_47]: (k9_relat_1(k1_xboole_0, A_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.75/1.86  tff(c_2839, plain, (![A_47]: (k9_relat_1('#skF_4', A_47)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2812, c_2812, c_50])).
% 4.75/1.86  tff(c_2950, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_522])).
% 4.75/1.86  tff(c_2954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2841, c_2950])).
% 4.75/1.86  tff(c_2955, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_564])).
% 4.75/1.86  tff(c_3005, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2955])).
% 4.75/1.86  tff(c_3009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_3005])).
% 4.75/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.75/1.86  
% 4.75/1.86  Inference rules
% 4.75/1.86  ----------------------
% 4.75/1.86  #Ref     : 0
% 4.75/1.86  #Sup     : 595
% 4.75/1.86  #Fact    : 0
% 4.75/1.86  #Define  : 0
% 4.75/1.86  #Split   : 10
% 4.75/1.86  #Chain   : 0
% 4.75/1.86  #Close   : 0
% 4.75/1.86  
% 4.75/1.86  Ordering : KBO
% 4.75/1.86  
% 4.75/1.86  Simplification rules
% 4.75/1.86  ----------------------
% 4.75/1.86  #Subsume      : 94
% 4.75/1.86  #Demod        : 653
% 4.75/1.86  #Tautology    : 328
% 4.75/1.86  #SimpNegUnit  : 20
% 4.75/1.86  #BackRed      : 105
% 4.75/1.86  
% 4.75/1.86  #Partial instantiations: 0
% 4.75/1.86  #Strategies tried      : 1
% 4.75/1.86  
% 4.75/1.86  Timing (in seconds)
% 4.75/1.86  ----------------------
% 4.75/1.86  Preprocessing        : 0.35
% 4.75/1.86  Parsing              : 0.19
% 4.75/1.86  CNF conversion       : 0.02
% 4.75/1.86  Main loop            : 0.74
% 4.75/1.86  Inferencing          : 0.25
% 4.75/1.86  Reduction            : 0.26
% 4.75/1.86  Demodulation         : 0.18
% 4.75/1.86  BG Simplification    : 0.03
% 4.75/1.86  Subsumption          : 0.15
% 4.75/1.86  Abstraction          : 0.03
% 4.75/1.86  MUC search           : 0.00
% 4.75/1.86  Cooper               : 0.00
% 4.75/1.86  Total                : 1.13
% 4.75/1.86  Index Insertion      : 0.00
% 4.75/1.86  Index Deletion       : 0.00
% 4.75/1.86  Index Matching       : 0.00
% 4.75/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
