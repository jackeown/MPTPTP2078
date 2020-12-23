%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 285 expanded)
%              Number of leaves         :   43 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 615 expanded)
%              Number of equality atoms :   50 ( 190 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_186,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_203,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_186])).

tff(c_44,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2365,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( k7_relset_1(A_277,B_278,C_279,D_280) = k9_relat_1(C_279,D_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2382,plain,(
    ! [D_280] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_280) = k9_relat_1('#skF_4',D_280) ),
    inference(resolution,[status(thm)],[c_70,c_2365])).

tff(c_2264,plain,(
    ! [B_265,A_266] :
      ( k1_tarski(k1_funct_1(B_265,A_266)) = k2_relat_1(B_265)
      | k1_tarski(A_266) != k1_relat_1(B_265)
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2270,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2264,c_66])).

tff(c_2282,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_74,c_2270])).

tff(c_2407,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2382,c_2282])).

tff(c_2408,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2407])).

tff(c_325,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_344,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_325])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2472,plain,(
    ! [B_293,C_294,A_295] :
      ( k2_tarski(B_293,C_294) = A_295
      | k1_tarski(C_294) = A_295
      | k1_tarski(B_293) = A_295
      | k1_xboole_0 = A_295
      | ~ r1_tarski(A_295,k2_tarski(B_293,C_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2485,plain,(
    ! [A_4,A_295] :
      ( k2_tarski(A_4,A_4) = A_295
      | k1_tarski(A_4) = A_295
      | k1_tarski(A_4) = A_295
      | k1_xboole_0 = A_295
      | ~ r1_tarski(A_295,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2472])).

tff(c_3422,plain,(
    ! [A_378,A_379] :
      ( k1_tarski(A_378) = A_379
      | k1_tarski(A_378) = A_379
      | k1_tarski(A_378) = A_379
      | k1_xboole_0 = A_379
      | ~ r1_tarski(A_379,k1_tarski(A_378)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2485])).

tff(c_3443,plain,(
    ! [A_380,B_381] :
      ( k1_tarski(A_380) = k1_relat_1(B_381)
      | k1_relat_1(B_381) = k1_xboole_0
      | ~ v4_relat_1(B_381,k1_tarski(A_380))
      | ~ v1_relat_1(B_381) ) ),
    inference(resolution,[status(thm)],[c_42,c_3422])).

tff(c_3485,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_3443])).

tff(c_3509,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_3485])).

tff(c_3510,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2408,c_3509])).

tff(c_2207,plain,(
    ! [A_259] :
      ( m1_subset_1(A_259,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_259),k2_relat_1(A_259))))
      | ~ v1_funct_1(A_259)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2232,plain,(
    ! [A_259] :
      ( r1_tarski(A_259,k2_zfmisc_1(k1_relat_1(A_259),k2_relat_1(A_259)))
      | ~ v1_funct_1(A_259)
      | ~ v1_relat_1(A_259) ) ),
    inference(resolution,[status(thm)],[c_2207,c_34])).

tff(c_3580,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3510,c_2232])).

tff(c_3635,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_74,c_30,c_3580])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_154])).

tff(c_3673,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3635,c_172])).

tff(c_3731,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3673,c_8])).

tff(c_32,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_204,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_217,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k9_relat_1(B_61,A_62),k2_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_222,plain,(
    ! [A_62] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_62),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_217])).

tff(c_226,plain,(
    ! [A_63] : r1_tarski(k9_relat_1(k1_xboole_0,A_63),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_222])).

tff(c_232,plain,(
    ! [A_63] : k9_relat_1(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_226,c_172])).

tff(c_3722,plain,(
    ! [A_63] : k9_relat_1('#skF_4',A_63) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3673,c_3673,c_232])).

tff(c_2392,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2382,c_66])).

tff(c_4100,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3722,c_2392])).

tff(c_4104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3731,c_4100])).

tff(c_4105,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2407])).

tff(c_4162,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_4105])).

tff(c_4166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_4162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.21/1.97  
% 5.21/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.21/1.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.21/1.97  
% 5.21/1.97  %Foreground sorts:
% 5.21/1.97  
% 5.21/1.97  
% 5.21/1.97  %Background operators:
% 5.21/1.97  
% 5.21/1.97  
% 5.21/1.97  %Foreground operators:
% 5.21/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.21/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.21/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.21/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.21/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.21/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.21/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.21/1.97  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.21/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.21/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.21/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.21/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.21/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.21/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.21/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.21/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.21/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.21/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.21/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.21/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.21/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.21/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.21/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.21/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.21/1.97  
% 5.40/1.98  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.40/1.98  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.40/1.98  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 5.40/1.98  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.40/1.98  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.40/1.98  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.40/1.98  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.40/1.98  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.40/1.98  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.40/1.98  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.40/1.98  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.40/1.98  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.40/1.98  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.40/1.98  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.40/1.98  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.40/1.98  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.40/1.98  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.40/1.98  tff(c_186, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.40/1.98  tff(c_203, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_186])).
% 5.40/1.98  tff(c_44, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.40/1.98  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.40/1.98  tff(c_30, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.40/1.98  tff(c_2365, plain, (![A_277, B_278, C_279, D_280]: (k7_relset_1(A_277, B_278, C_279, D_280)=k9_relat_1(C_279, D_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.40/1.98  tff(c_2382, plain, (![D_280]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_280)=k9_relat_1('#skF_4', D_280))), inference(resolution, [status(thm)], [c_70, c_2365])).
% 5.40/1.98  tff(c_2264, plain, (![B_265, A_266]: (k1_tarski(k1_funct_1(B_265, A_266))=k2_relat_1(B_265) | k1_tarski(A_266)!=k1_relat_1(B_265) | ~v1_funct_1(B_265) | ~v1_relat_1(B_265))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.40/1.98  tff(c_66, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.40/1.98  tff(c_2270, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2264, c_66])).
% 5.40/1.98  tff(c_2282, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_74, c_2270])).
% 5.40/1.98  tff(c_2407, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2382, c_2282])).
% 5.40/1.98  tff(c_2408, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2407])).
% 5.40/1.98  tff(c_325, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.40/1.98  tff(c_344, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_325])).
% 5.40/1.98  tff(c_42, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.40/1.98  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.40/1.98  tff(c_2472, plain, (![B_293, C_294, A_295]: (k2_tarski(B_293, C_294)=A_295 | k1_tarski(C_294)=A_295 | k1_tarski(B_293)=A_295 | k1_xboole_0=A_295 | ~r1_tarski(A_295, k2_tarski(B_293, C_294)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.40/1.98  tff(c_2485, plain, (![A_4, A_295]: (k2_tarski(A_4, A_4)=A_295 | k1_tarski(A_4)=A_295 | k1_tarski(A_4)=A_295 | k1_xboole_0=A_295 | ~r1_tarski(A_295, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2472])).
% 5.40/1.98  tff(c_3422, plain, (![A_378, A_379]: (k1_tarski(A_378)=A_379 | k1_tarski(A_378)=A_379 | k1_tarski(A_378)=A_379 | k1_xboole_0=A_379 | ~r1_tarski(A_379, k1_tarski(A_378)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2485])).
% 5.40/1.98  tff(c_3443, plain, (![A_380, B_381]: (k1_tarski(A_380)=k1_relat_1(B_381) | k1_relat_1(B_381)=k1_xboole_0 | ~v4_relat_1(B_381, k1_tarski(A_380)) | ~v1_relat_1(B_381))), inference(resolution, [status(thm)], [c_42, c_3422])).
% 5.40/1.98  tff(c_3485, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_344, c_3443])).
% 5.40/1.98  tff(c_3509, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_203, c_3485])).
% 5.40/1.98  tff(c_3510, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2408, c_3509])).
% 5.40/1.98  tff(c_2207, plain, (![A_259]: (m1_subset_1(A_259, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_259), k2_relat_1(A_259)))) | ~v1_funct_1(A_259) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.40/1.98  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.40/1.98  tff(c_2232, plain, (![A_259]: (r1_tarski(A_259, k2_zfmisc_1(k1_relat_1(A_259), k2_relat_1(A_259))) | ~v1_funct_1(A_259) | ~v1_relat_1(A_259))), inference(resolution, [status(thm)], [c_2207, c_34])).
% 5.40/1.98  tff(c_3580, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3510, c_2232])).
% 5.40/1.98  tff(c_3635, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_74, c_30, c_3580])).
% 5.40/1.98  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.40/1.98  tff(c_154, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.40/1.98  tff(c_172, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_154])).
% 5.40/1.98  tff(c_3673, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3635, c_172])).
% 5.40/1.98  tff(c_3731, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3673, c_8])).
% 5.40/1.98  tff(c_32, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.40/1.98  tff(c_204, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_186])).
% 5.40/1.98  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.40/1.98  tff(c_217, plain, (![B_61, A_62]: (r1_tarski(k9_relat_1(B_61, A_62), k2_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.40/1.98  tff(c_222, plain, (![A_62]: (r1_tarski(k9_relat_1(k1_xboole_0, A_62), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_217])).
% 5.40/1.98  tff(c_226, plain, (![A_63]: (r1_tarski(k9_relat_1(k1_xboole_0, A_63), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_222])).
% 5.40/1.98  tff(c_232, plain, (![A_63]: (k9_relat_1(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_226, c_172])).
% 5.40/1.98  tff(c_3722, plain, (![A_63]: (k9_relat_1('#skF_4', A_63)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3673, c_3673, c_232])).
% 5.40/1.98  tff(c_2392, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2382, c_66])).
% 5.40/1.98  tff(c_4100, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3722, c_2392])).
% 5.40/1.98  tff(c_4104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3731, c_4100])).
% 5.40/1.98  tff(c_4105, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2407])).
% 5.40/1.98  tff(c_4162, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_4105])).
% 5.40/1.98  tff(c_4166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_4162])).
% 5.40/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/1.98  
% 5.40/1.98  Inference rules
% 5.40/1.98  ----------------------
% 5.40/1.98  #Ref     : 0
% 5.40/1.98  #Sup     : 862
% 5.40/1.98  #Fact    : 0
% 5.40/1.98  #Define  : 0
% 5.40/1.98  #Split   : 4
% 5.40/1.98  #Chain   : 0
% 5.40/1.98  #Close   : 0
% 5.40/1.98  
% 5.40/1.98  Ordering : KBO
% 5.40/1.98  
% 5.40/1.98  Simplification rules
% 5.40/1.98  ----------------------
% 5.40/1.98  #Subsume      : 83
% 5.40/1.98  #Demod        : 1473
% 5.40/1.98  #Tautology    : 491
% 5.40/1.98  #SimpNegUnit  : 2
% 5.40/1.98  #BackRed      : 119
% 5.40/1.98  
% 5.40/1.98  #Partial instantiations: 0
% 5.40/1.98  #Strategies tried      : 1
% 5.40/1.98  
% 5.40/1.98  Timing (in seconds)
% 5.40/1.98  ----------------------
% 5.40/1.99  Preprocessing        : 0.33
% 5.40/1.99  Parsing              : 0.17
% 5.40/1.99  CNF conversion       : 0.02
% 5.40/1.99  Main loop            : 0.87
% 5.40/1.99  Inferencing          : 0.30
% 5.40/1.99  Reduction            : 0.32
% 5.40/1.99  Demodulation         : 0.24
% 5.40/1.99  BG Simplification    : 0.03
% 5.40/1.99  Subsumption          : 0.15
% 5.40/1.99  Abstraction          : 0.04
% 5.40/1.99  MUC search           : 0.00
% 5.40/1.99  Cooper               : 0.00
% 5.40/1.99  Total                : 1.24
% 5.40/1.99  Index Insertion      : 0.00
% 5.40/1.99  Index Deletion       : 0.00
% 5.40/1.99  Index Matching       : 0.00
% 5.40/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
