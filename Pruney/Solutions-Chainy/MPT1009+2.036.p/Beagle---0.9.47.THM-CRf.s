%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 14.17s
% Output     : CNFRefutation 14.17s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 809 expanded)
%              Number of leaves         :   42 ( 290 expanded)
%              Depth                    :   19
%              Number of atoms          :  389 (1835 expanded)
%              Number of equality atoms :  137 ( 457 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
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

tff(f_88,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_178,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_191,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_178])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_678,plain,(
    ! [D_149,B_150,C_151,A_152] :
      ( m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(B_150,C_151)))
      | ~ r1_tarski(k1_relat_1(D_149),B_150)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_152,C_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_703,plain,(
    ! [B_157] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_157,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_157) ) ),
    inference(resolution,[status(thm)],[c_68,c_678])).

tff(c_723,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_703])).

tff(c_745,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    ! [C_72] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_178])).

tff(c_242,plain,(
    ! [A_76] :
      ( v1_relat_1(A_76)
      | ~ r1_tarski(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_192])).

tff(c_251,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_242])).

tff(c_355,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_406,plain,(
    ! [A_114,A_115,B_116] :
      ( v4_relat_1(A_114,A_115)
      | ~ r1_tarski(A_114,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_42,c_355])).

tff(c_431,plain,(
    ! [A_115,B_116] : v4_relat_1(k2_zfmisc_1(A_115,B_116),A_115) ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_377,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k1_relat_1(B_108),A_109)
      | ~ v4_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_198,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_510,plain,(
    ! [B_128] :
      ( k1_relat_1(B_128) = k1_xboole_0
      | ~ v4_relat_1(B_128,k1_xboole_0)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_377,c_228])).

tff(c_514,plain,(
    ! [B_116] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_116)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_116)) ) ),
    inference(resolution,[status(thm)],[c_431,c_510])).

tff(c_525,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_20,c_20,c_514])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_434,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(k1_funct_1(B_118,A_119)) = k2_relat_1(B_118)
      | k1_tarski(A_119) != k1_relat_1(B_118)
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_440,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_64])).

tff(c_461,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_72,c_440])).

tff(c_500,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_370,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_355])).

tff(c_46,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_756,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k1_enumset1(A_159,B_160,C_161) = D_162
      | k2_tarski(A_159,C_161) = D_162
      | k2_tarski(B_160,C_161) = D_162
      | k2_tarski(A_159,B_160) = D_162
      | k1_tarski(C_161) = D_162
      | k1_tarski(B_160) = D_162
      | k1_tarski(A_159) = D_162
      | k1_xboole_0 = D_162
      | ~ r1_tarski(D_162,k1_enumset1(A_159,B_160,C_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_781,plain,(
    ! [A_5,B_6,D_162] :
      ( k1_enumset1(A_5,A_5,B_6) = D_162
      | k2_tarski(A_5,B_6) = D_162
      | k2_tarski(A_5,B_6) = D_162
      | k2_tarski(A_5,A_5) = D_162
      | k1_tarski(B_6) = D_162
      | k1_tarski(A_5) = D_162
      | k1_tarski(A_5) = D_162
      | k1_xboole_0 = D_162
      | ~ r1_tarski(D_162,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_756])).

tff(c_3312,plain,(
    ! [A_376,B_377,D_378] :
      ( k2_tarski(A_376,B_377) = D_378
      | k2_tarski(A_376,B_377) = D_378
      | k2_tarski(A_376,B_377) = D_378
      | k1_tarski(A_376) = D_378
      | k1_tarski(B_377) = D_378
      | k1_tarski(A_376) = D_378
      | k1_tarski(A_376) = D_378
      | k1_xboole_0 = D_378
      | ~ r1_tarski(D_378,k2_tarski(A_376,B_377)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_781])).

tff(c_3325,plain,(
    ! [A_4,D_378] :
      ( k2_tarski(A_4,A_4) = D_378
      | k2_tarski(A_4,A_4) = D_378
      | k2_tarski(A_4,A_4) = D_378
      | k1_tarski(A_4) = D_378
      | k1_tarski(A_4) = D_378
      | k1_tarski(A_4) = D_378
      | k1_tarski(A_4) = D_378
      | k1_xboole_0 = D_378
      | ~ r1_tarski(D_378,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3312])).

tff(c_10457,plain,(
    ! [A_577,D_578] :
      ( k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_tarski(A_577) = D_578
      | k1_xboole_0 = D_578
      | ~ r1_tarski(D_578,k1_tarski(A_577)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_3325])).

tff(c_10497,plain,(
    ! [A_583,B_584] :
      ( k1_tarski(A_583) = k1_relat_1(B_584)
      | k1_relat_1(B_584) = k1_xboole_0
      | ~ v4_relat_1(B_584,k1_tarski(A_583))
      | ~ v1_relat_1(B_584) ) ),
    inference(resolution,[status(thm)],[c_46,c_10457])).

tff(c_10559,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_10497])).

tff(c_10592,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_10559])).

tff(c_10593,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_10592])).

tff(c_400,plain,(
    ! [C_110,A_111] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_355])).

tff(c_404,plain,(
    ! [A_16,A_111] :
      ( v4_relat_1(A_16,A_111)
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_255,plain,(
    ! [A_77,A_78,B_79] :
      ( v1_relat_1(A_77)
      | ~ r1_tarski(A_77,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_273,plain,(
    ! [A_78,B_79] : v1_relat_1(k2_zfmisc_1(A_78,B_79)) ),
    inference(resolution,[status(thm)],[c_6,c_255])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_808,plain,(
    ! [B_163] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_163,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_163) ) ),
    inference(resolution,[status(thm)],[c_703,c_40])).

tff(c_820,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_808])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_966,plain,(
    ! [B_176,A_177] :
      ( k1_relat_1(B_176) = A_177
      | ~ r1_tarski(A_177,k1_relat_1(B_176))
      | ~ v4_relat_1(B_176,A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(resolution,[status(thm)],[c_377,c_2])).

tff(c_4147,plain,(
    ! [B_422,B_421] :
      ( k1_relat_1(B_422) = k1_relat_1(B_421)
      | ~ v4_relat_1(B_422,k1_relat_1(B_421))
      | ~ v1_relat_1(B_422)
      | ~ v4_relat_1(B_421,k1_relat_1(B_422))
      | ~ v1_relat_1(B_421) ) ),
    inference(resolution,[status(thm)],[c_46,c_966])).

tff(c_4242,plain,(
    ! [B_423,A_424] :
      ( k1_relat_1(B_423) = k1_relat_1(A_424)
      | ~ v1_relat_1(A_424)
      | ~ v4_relat_1(B_423,k1_relat_1(A_424))
      | ~ v1_relat_1(B_423)
      | ~ r1_tarski(A_424,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_404,c_4147])).

tff(c_4303,plain,(
    ! [A_424,B_116] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_424),B_116)) = k1_relat_1(A_424)
      | ~ v1_relat_1(A_424)
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(A_424),B_116))
      | ~ r1_tarski(A_424,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_431,c_4242])).

tff(c_4356,plain,(
    ! [A_425,B_426] :
      ( k1_relat_1(k2_zfmisc_1(k1_relat_1(A_425),B_426)) = k1_relat_1(A_425)
      | ~ v1_relat_1(A_425)
      | ~ r1_tarski(A_425,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_4303])).

tff(c_2111,plain,(
    ! [A_294,B_295,C_296,A_297] :
      ( m1_subset_1(A_294,k1_zfmisc_1(k2_zfmisc_1(B_295,C_296)))
      | ~ r1_tarski(k1_relat_1(A_294),B_295)
      | ~ r1_tarski(A_294,k2_zfmisc_1(A_297,C_296)) ) ),
    inference(resolution,[status(thm)],[c_42,c_678])).

tff(c_2441,plain,(
    ! [A_317,C_318,B_319] :
      ( m1_subset_1(k2_zfmisc_1(A_317,C_318),k1_zfmisc_1(k2_zfmisc_1(B_319,C_318)))
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(A_317,C_318)),B_319) ) ),
    inference(resolution,[status(thm)],[c_6,c_2111])).

tff(c_58,plain,(
    ! [C_30,A_28,B_29] :
      ( v4_relat_1(C_30,A_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2472,plain,(
    ! [A_317,C_318,B_319] :
      ( v4_relat_1(k2_zfmisc_1(A_317,C_318),B_319)
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(A_317,C_318)),B_319) ) ),
    inference(resolution,[status(thm)],[c_2441,c_58])).

tff(c_4891,plain,(
    ! [A_432,B_433,B_434] :
      ( v4_relat_1(k2_zfmisc_1(k1_relat_1(A_432),B_433),B_434)
      | ~ r1_tarski(k1_relat_1(A_432),B_434)
      | ~ v1_relat_1(A_432)
      | ~ r1_tarski(A_432,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4356,c_2472])).

tff(c_2556,plain,(
    ! [A_329,B_330] :
      ( m1_subset_1(k2_zfmisc_1(A_329,B_330),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(A_329,B_330)),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2441])).

tff(c_2559,plain,(
    ! [A_329,B_330] :
      ( m1_subset_1(k2_zfmisc_1(A_329,B_330),k1_zfmisc_1(k1_xboole_0))
      | ~ v4_relat_1(k2_zfmisc_1(A_329,B_330),k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_329,B_330)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2556])).

tff(c_2568,plain,(
    ! [A_329,B_330] :
      ( m1_subset_1(k2_zfmisc_1(A_329,B_330),k1_zfmisc_1(k1_xboole_0))
      | ~ v4_relat_1(k2_zfmisc_1(A_329,B_330),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_2559])).

tff(c_1713,plain,(
    ! [D_255,B_256,B_257] :
      ( m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(B_256,B_257)))
      | ~ r1_tarski(k1_relat_1(D_255),B_256)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_678])).

tff(c_1742,plain,(
    ! [D_258,B_259,B_260] :
      ( r1_tarski(D_258,k2_zfmisc_1(B_259,B_260))
      | ~ r1_tarski(k1_relat_1(D_258),B_259)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1713,c_40])).

tff(c_1762,plain,(
    ! [D_261,B_262] :
      ( r1_tarski(D_261,k2_zfmisc_1(k1_relat_1(D_261),B_262))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1742])).

tff(c_2934,plain,(
    ! [D_365,B_366] :
      ( k2_zfmisc_1(k1_relat_1(D_365),B_366) = D_365
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(D_365),B_366),D_365)
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1762,c_2])).

tff(c_2959,plain,(
    ! [D_365] :
      ( k2_zfmisc_1(k1_relat_1(D_365),k1_xboole_0) = D_365
      | ~ r1_tarski(k1_xboole_0,D_365)
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2934])).

tff(c_2975,plain,(
    ! [D_367] :
      ( k1_xboole_0 = D_367
      | ~ m1_subset_1(D_367,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18,c_2959])).

tff(c_2986,plain,(
    ! [A_329,B_330] :
      ( k2_zfmisc_1(A_329,B_330) = k1_xboole_0
      | ~ v4_relat_1(k2_zfmisc_1(A_329,B_330),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2568,c_2975])).

tff(c_4989,plain,(
    ! [A_435,B_436] :
      ( k2_zfmisc_1(k1_relat_1(A_435),B_436) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(A_435),k1_xboole_0)
      | ~ v1_relat_1(A_435)
      | ~ r1_tarski(A_435,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4891,c_2986])).

tff(c_5022,plain,(
    ! [B_437,B_438] :
      ( k2_zfmisc_1(k1_relat_1(B_437),B_438) = k1_xboole_0
      | ~ r1_tarski(B_437,k1_xboole_0)
      | ~ v4_relat_1(B_437,k1_xboole_0)
      | ~ v1_relat_1(B_437) ) ),
    inference(resolution,[status(thm)],[c_46,c_4989])).

tff(c_2223,plain,(
    ! [A_304,B_305,B_306] :
      ( m1_subset_1(A_304,k1_zfmisc_1(k2_zfmisc_1(B_305,B_306)))
      | ~ r1_tarski(k1_relat_1(A_304),B_305)
      | ~ r1_tarski(A_304,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2111])).

tff(c_2252,plain,(
    ! [A_307,B_308,B_309] :
      ( r1_tarski(A_307,k2_zfmisc_1(B_308,B_309))
      | ~ r1_tarski(k1_relat_1(A_307),B_308)
      | ~ r1_tarski(A_307,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2223,c_40])).

tff(c_2280,plain,(
    ! [A_310,B_311] :
      ( r1_tarski(A_310,k2_zfmisc_1(k1_relat_1(A_310),B_311))
      | ~ r1_tarski(A_310,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_2252])).

tff(c_2340,plain,(
    ! [A_310,B_311] :
      ( k2_zfmisc_1(k1_relat_1(A_310),B_311) = A_310
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_310),B_311),A_310)
      | ~ r1_tarski(A_310,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2280,c_2])).

tff(c_5073,plain,(
    ! [B_437,B_438] :
      ( k2_zfmisc_1(k1_relat_1(B_437),B_438) = B_437
      | ~ r1_tarski(k1_xboole_0,B_437)
      | ~ r1_tarski(B_437,k1_xboole_0)
      | ~ r1_tarski(B_437,k1_xboole_0)
      | ~ v4_relat_1(B_437,k1_xboole_0)
      | ~ v1_relat_1(B_437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5022,c_2340])).

tff(c_5474,plain,(
    ! [B_444,B_445] :
      ( k2_zfmisc_1(k1_relat_1(B_444),B_445) = B_444
      | ~ r1_tarski(B_444,k1_xboole_0)
      | ~ v4_relat_1(B_444,k1_xboole_0)
      | ~ v1_relat_1(B_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5073])).

tff(c_332,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_346,plain,(
    ! [A_16,B_97,A_98] :
      ( v5_relat_1(A_16,B_97)
      | ~ r1_tarski(A_16,k2_zfmisc_1(A_98,B_97)) ) ),
    inference(resolution,[status(thm)],[c_42,c_332])).

tff(c_6751,plain,(
    ! [A_467,B_468,B_469] :
      ( v5_relat_1(A_467,B_468)
      | ~ r1_tarski(A_467,B_469)
      | ~ r1_tarski(B_469,k1_xboole_0)
      | ~ v4_relat_1(B_469,k1_xboole_0)
      | ~ v1_relat_1(B_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5474,c_346])).

tff(c_6785,plain,(
    ! [B_468] :
      ( v5_relat_1('#skF_4',B_468)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0)
      | ~ v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_820,c_6751])).

tff(c_6850,plain,(
    ! [B_468] :
      ( v5_relat_1('#skF_4',B_468)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0)
      | ~ v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_6785])).

tff(c_7364,plain,(
    ~ v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_6850])).

tff(c_7390,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_404,c_7364])).

tff(c_10596,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10593,c_7390])).

tff(c_10615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_10596])).

tff(c_10617,plain,(
    v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6850])).

tff(c_10635,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10617,c_2986])).

tff(c_838,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_820,c_2])).

tff(c_1124,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_10647,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10635,c_1124])).

tff(c_10652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10647])).

tff(c_10653,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_62,plain,(
    ! [D_38,B_36,C_37,A_35] :
      ( m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(B_36,C_37)))
      | ~ r1_tarski(k1_relat_1(D_38),B_36)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_35,C_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_11849,plain,(
    ! [D_658,B_659] :
      ( m1_subset_1(D_658,k1_zfmisc_1(k2_zfmisc_1(B_659,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(D_658),B_659)
      | ~ m1_subset_1(D_658,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10653,c_62])).

tff(c_11937,plain,(
    ! [D_663] :
      ( m1_subset_1(D_663,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(D_663),k1_xboole_0)
      | ~ m1_subset_1(D_663,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_11849])).

tff(c_11952,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_11937])).

tff(c_11966,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11952])).

tff(c_11976,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11966])).

tff(c_11979,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_11976])).

tff(c_11983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11979])).

tff(c_11984,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_11966])).

tff(c_15427,plain,(
    ! [A_814,B_815,D_816] :
      ( k2_tarski(A_814,B_815) = D_816
      | k2_tarski(A_814,B_815) = D_816
      | k2_tarski(A_814,B_815) = D_816
      | k1_tarski(A_814) = D_816
      | k1_tarski(B_815) = D_816
      | k1_tarski(A_814) = D_816
      | k1_tarski(A_814) = D_816
      | k1_xboole_0 = D_816
      | ~ r1_tarski(D_816,k2_tarski(A_814,B_815)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_781])).

tff(c_15440,plain,(
    ! [A_4,D_816] :
      ( k2_tarski(A_4,A_4) = D_816
      | k2_tarski(A_4,A_4) = D_816
      | k2_tarski(A_4,A_4) = D_816
      | k1_tarski(A_4) = D_816
      | k1_tarski(A_4) = D_816
      | k1_tarski(A_4) = D_816
      | k1_tarski(A_4) = D_816
      | k1_xboole_0 = D_816
      | ~ r1_tarski(D_816,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15427])).

tff(c_29371,plain,(
    ! [A_1085,D_1086] :
      ( k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_tarski(A_1085) = D_1086
      | k1_xboole_0 = D_1086
      | ~ r1_tarski(D_1086,k1_tarski(A_1085)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_15440])).

tff(c_32461,plain,(
    ! [A_1123,B_1124] :
      ( k1_tarski(A_1123) = k1_relat_1(B_1124)
      | k1_relat_1(B_1124) = k1_xboole_0
      | ~ v4_relat_1(B_1124,k1_tarski(A_1123))
      | ~ v1_relat_1(B_1124) ) ),
    inference(resolution,[status(thm)],[c_46,c_29371])).

tff(c_32527,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_32461])).

tff(c_32561,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_32527])).

tff(c_32562,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_32561])).

tff(c_12233,plain,(
    ! [D_676,B_677,B_678] :
      ( m1_subset_1(D_676,k1_zfmisc_1(k2_zfmisc_1(B_677,B_678)))
      | ~ r1_tarski(k1_relat_1(D_676),B_677)
      | ~ m1_subset_1(D_676,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_678])).

tff(c_12323,plain,(
    ! [D_681,B_682,B_683] :
      ( r1_tarski(D_681,k2_zfmisc_1(B_682,B_683))
      | ~ r1_tarski(k1_relat_1(D_681),B_682)
      | ~ m1_subset_1(D_681,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12233,c_40])).

tff(c_12355,plain,(
    ! [D_684,B_685] :
      ( r1_tarski(D_684,k2_zfmisc_1(k1_relat_1(D_684),B_685))
      | ~ m1_subset_1(D_684,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_12323])).

tff(c_726,plain,(
    ! [B_157] :
      ( v4_relat_1('#skF_4',B_157)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_157) ) ),
    inference(resolution,[status(thm)],[c_703,c_58])).

tff(c_12422,plain,(
    ! [B_685] :
      ( v4_relat_1('#skF_4',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')),B_685))
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12355,c_726])).

tff(c_12435,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_12422])).

tff(c_32584,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32562,c_12435])).

tff(c_32619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11984,c_32584])).

tff(c_32621,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_12422])).

tff(c_32635,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32621,c_40])).

tff(c_32644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_32635])).

tff(c_32645,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_32661,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32645,c_40])).

tff(c_32715,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32661,c_228])).

tff(c_32742,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32715,c_8])).

tff(c_50,plain,(
    ! [A_22] : k9_relat_1(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32741,plain,(
    ! [A_22] : k9_relat_1('#skF_4',A_22) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32715,c_32715,c_50])).

tff(c_550,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k7_relset_1(A_129,B_130,C_131,D_132) = k9_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_561,plain,(
    ! [D_132] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_132) = k9_relat_1('#skF_4',D_132) ),
    inference(resolution,[status(thm)],[c_68,c_550])).

tff(c_588,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_64])).

tff(c_32881,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32741,c_588])).

tff(c_32885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32742,c_32881])).

tff(c_32887,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_32892,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32887,c_68])).

tff(c_60,plain,(
    ! [A_31,B_32,C_33,D_34] :
      ( k7_relset_1(A_31,B_32,C_33,D_34) = k9_relat_1(C_33,D_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_33005,plain,(
    ! [D_34] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_34) = k9_relat_1('#skF_4',D_34) ),
    inference(resolution,[status(thm)],[c_32892,c_60])).

tff(c_32886,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_33161,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32887,c_32886])).

tff(c_33162,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33005,c_33161])).

tff(c_33242,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_33162])).

tff(c_33246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_33242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:25:47 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.17/6.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.17/6.11  
% 14.17/6.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.17/6.11  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.17/6.11  
% 14.17/6.11  %Foreground sorts:
% 14.17/6.11  
% 14.17/6.11  
% 14.17/6.11  %Background operators:
% 14.17/6.11  
% 14.17/6.11  
% 14.17/6.11  %Foreground operators:
% 14.17/6.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.17/6.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.17/6.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.17/6.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.17/6.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.17/6.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.17/6.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.17/6.11  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 14.17/6.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.17/6.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.17/6.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.17/6.11  tff('#skF_2', type, '#skF_2': $i).
% 14.17/6.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.17/6.11  tff('#skF_3', type, '#skF_3': $i).
% 14.17/6.11  tff('#skF_1', type, '#skF_1': $i).
% 14.17/6.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.17/6.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.17/6.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.17/6.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.17/6.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.17/6.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.17/6.11  tff('#skF_4', type, '#skF_4': $i).
% 14.17/6.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.17/6.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.17/6.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.17/6.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.17/6.11  
% 14.17/6.14  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 14.17/6.14  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.17/6.14  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 14.17/6.14  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.17/6.14  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 14.17/6.14  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.17/6.14  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.17/6.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.17/6.14  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.17/6.14  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.17/6.14  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 14.17/6.14  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.17/6.14  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 14.17/6.14  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 14.17/6.14  tff(f_88, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 14.17/6.14  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.17/6.14  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.17/6.14  tff(c_178, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.17/6.14  tff(c_191, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_178])).
% 14.17/6.14  tff(c_48, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.17/6.14  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.17/6.14  tff(c_678, plain, (![D_149, B_150, C_151, A_152]: (m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(B_150, C_151))) | ~r1_tarski(k1_relat_1(D_149), B_150) | ~m1_subset_1(D_149, k1_zfmisc_1(k2_zfmisc_1(A_152, C_151))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.17/6.14  tff(c_703, plain, (![B_157]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_157, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_157))), inference(resolution, [status(thm)], [c_68, c_678])).
% 14.17/6.14  tff(c_723, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_703])).
% 14.17/6.14  tff(c_745, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_723])).
% 14.17/6.14  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.17/6.14  tff(c_42, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.17/6.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.17/6.14  tff(c_18, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.17/6.14  tff(c_192, plain, (![C_72]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_178])).
% 14.17/6.14  tff(c_242, plain, (![A_76]: (v1_relat_1(A_76) | ~r1_tarski(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_192])).
% 14.17/6.14  tff(c_251, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_242])).
% 14.17/6.14  tff(c_355, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.17/6.14  tff(c_406, plain, (![A_114, A_115, B_116]: (v4_relat_1(A_114, A_115) | ~r1_tarski(A_114, k2_zfmisc_1(A_115, B_116)))), inference(resolution, [status(thm)], [c_42, c_355])).
% 14.17/6.14  tff(c_431, plain, (![A_115, B_116]: (v4_relat_1(k2_zfmisc_1(A_115, B_116), A_115))), inference(resolution, [status(thm)], [c_6, c_406])).
% 14.17/6.14  tff(c_377, plain, (![B_108, A_109]: (r1_tarski(k1_relat_1(B_108), A_109) | ~v4_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.17/6.14  tff(c_198, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.17/6.14  tff(c_228, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_198])).
% 14.17/6.14  tff(c_510, plain, (![B_128]: (k1_relat_1(B_128)=k1_xboole_0 | ~v4_relat_1(B_128, k1_xboole_0) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_377, c_228])).
% 14.17/6.14  tff(c_514, plain, (![B_116]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_116))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_116)))), inference(resolution, [status(thm)], [c_431, c_510])).
% 14.17/6.14  tff(c_525, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_251, c_20, c_20, c_514])).
% 14.17/6.14  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.17/6.14  tff(c_434, plain, (![B_118, A_119]: (k1_tarski(k1_funct_1(B_118, A_119))=k2_relat_1(B_118) | k1_tarski(A_119)!=k1_relat_1(B_118) | ~v1_funct_1(B_118) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.17/6.14  tff(c_64, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.17/6.14  tff(c_440, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_434, c_64])).
% 14.17/6.14  tff(c_461, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_72, c_440])).
% 14.17/6.14  tff(c_500, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_461])).
% 14.17/6.14  tff(c_370, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_355])).
% 14.17/6.14  tff(c_46, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.17/6.14  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.17/6.14  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.17/6.14  tff(c_756, plain, (![A_159, B_160, C_161, D_162]: (k1_enumset1(A_159, B_160, C_161)=D_162 | k2_tarski(A_159, C_161)=D_162 | k2_tarski(B_160, C_161)=D_162 | k2_tarski(A_159, B_160)=D_162 | k1_tarski(C_161)=D_162 | k1_tarski(B_160)=D_162 | k1_tarski(A_159)=D_162 | k1_xboole_0=D_162 | ~r1_tarski(D_162, k1_enumset1(A_159, B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.17/6.14  tff(c_781, plain, (![A_5, B_6, D_162]: (k1_enumset1(A_5, A_5, B_6)=D_162 | k2_tarski(A_5, B_6)=D_162 | k2_tarski(A_5, B_6)=D_162 | k2_tarski(A_5, A_5)=D_162 | k1_tarski(B_6)=D_162 | k1_tarski(A_5)=D_162 | k1_tarski(A_5)=D_162 | k1_xboole_0=D_162 | ~r1_tarski(D_162, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_756])).
% 14.17/6.14  tff(c_3312, plain, (![A_376, B_377, D_378]: (k2_tarski(A_376, B_377)=D_378 | k2_tarski(A_376, B_377)=D_378 | k2_tarski(A_376, B_377)=D_378 | k1_tarski(A_376)=D_378 | k1_tarski(B_377)=D_378 | k1_tarski(A_376)=D_378 | k1_tarski(A_376)=D_378 | k1_xboole_0=D_378 | ~r1_tarski(D_378, k2_tarski(A_376, B_377)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_781])).
% 14.17/6.14  tff(c_3325, plain, (![A_4, D_378]: (k2_tarski(A_4, A_4)=D_378 | k2_tarski(A_4, A_4)=D_378 | k2_tarski(A_4, A_4)=D_378 | k1_tarski(A_4)=D_378 | k1_tarski(A_4)=D_378 | k1_tarski(A_4)=D_378 | k1_tarski(A_4)=D_378 | k1_xboole_0=D_378 | ~r1_tarski(D_378, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3312])).
% 14.17/6.14  tff(c_10457, plain, (![A_577, D_578]: (k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_tarski(A_577)=D_578 | k1_xboole_0=D_578 | ~r1_tarski(D_578, k1_tarski(A_577)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_3325])).
% 14.17/6.14  tff(c_10497, plain, (![A_583, B_584]: (k1_tarski(A_583)=k1_relat_1(B_584) | k1_relat_1(B_584)=k1_xboole_0 | ~v4_relat_1(B_584, k1_tarski(A_583)) | ~v1_relat_1(B_584))), inference(resolution, [status(thm)], [c_46, c_10457])).
% 14.17/6.14  tff(c_10559, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_370, c_10497])).
% 14.17/6.14  tff(c_10592, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_10559])).
% 14.17/6.14  tff(c_10593, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_500, c_10592])).
% 14.17/6.14  tff(c_400, plain, (![C_110, A_111]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_355])).
% 14.17/6.14  tff(c_404, plain, (![A_16, A_111]: (v4_relat_1(A_16, A_111) | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_400])).
% 14.17/6.14  tff(c_255, plain, (![A_77, A_78, B_79]: (v1_relat_1(A_77) | ~r1_tarski(A_77, k2_zfmisc_1(A_78, B_79)))), inference(resolution, [status(thm)], [c_42, c_178])).
% 14.17/6.14  tff(c_273, plain, (![A_78, B_79]: (v1_relat_1(k2_zfmisc_1(A_78, B_79)))), inference(resolution, [status(thm)], [c_6, c_255])).
% 14.17/6.14  tff(c_40, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.17/6.14  tff(c_808, plain, (![B_163]: (r1_tarski('#skF_4', k2_zfmisc_1(B_163, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_163))), inference(resolution, [status(thm)], [c_703, c_40])).
% 14.17/6.14  tff(c_820, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_808])).
% 14.17/6.14  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.17/6.14  tff(c_966, plain, (![B_176, A_177]: (k1_relat_1(B_176)=A_177 | ~r1_tarski(A_177, k1_relat_1(B_176)) | ~v4_relat_1(B_176, A_177) | ~v1_relat_1(B_176))), inference(resolution, [status(thm)], [c_377, c_2])).
% 14.17/6.14  tff(c_4147, plain, (![B_422, B_421]: (k1_relat_1(B_422)=k1_relat_1(B_421) | ~v4_relat_1(B_422, k1_relat_1(B_421)) | ~v1_relat_1(B_422) | ~v4_relat_1(B_421, k1_relat_1(B_422)) | ~v1_relat_1(B_421))), inference(resolution, [status(thm)], [c_46, c_966])).
% 14.17/6.14  tff(c_4242, plain, (![B_423, A_424]: (k1_relat_1(B_423)=k1_relat_1(A_424) | ~v1_relat_1(A_424) | ~v4_relat_1(B_423, k1_relat_1(A_424)) | ~v1_relat_1(B_423) | ~r1_tarski(A_424, k1_xboole_0))), inference(resolution, [status(thm)], [c_404, c_4147])).
% 14.17/6.14  tff(c_4303, plain, (![A_424, B_116]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_424), B_116))=k1_relat_1(A_424) | ~v1_relat_1(A_424) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(A_424), B_116)) | ~r1_tarski(A_424, k1_xboole_0))), inference(resolution, [status(thm)], [c_431, c_4242])).
% 14.17/6.14  tff(c_4356, plain, (![A_425, B_426]: (k1_relat_1(k2_zfmisc_1(k1_relat_1(A_425), B_426))=k1_relat_1(A_425) | ~v1_relat_1(A_425) | ~r1_tarski(A_425, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_4303])).
% 14.17/6.14  tff(c_2111, plain, (![A_294, B_295, C_296, A_297]: (m1_subset_1(A_294, k1_zfmisc_1(k2_zfmisc_1(B_295, C_296))) | ~r1_tarski(k1_relat_1(A_294), B_295) | ~r1_tarski(A_294, k2_zfmisc_1(A_297, C_296)))), inference(resolution, [status(thm)], [c_42, c_678])).
% 14.17/6.14  tff(c_2441, plain, (![A_317, C_318, B_319]: (m1_subset_1(k2_zfmisc_1(A_317, C_318), k1_zfmisc_1(k2_zfmisc_1(B_319, C_318))) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(A_317, C_318)), B_319))), inference(resolution, [status(thm)], [c_6, c_2111])).
% 14.17/6.14  tff(c_58, plain, (![C_30, A_28, B_29]: (v4_relat_1(C_30, A_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.17/6.14  tff(c_2472, plain, (![A_317, C_318, B_319]: (v4_relat_1(k2_zfmisc_1(A_317, C_318), B_319) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(A_317, C_318)), B_319))), inference(resolution, [status(thm)], [c_2441, c_58])).
% 14.17/6.14  tff(c_4891, plain, (![A_432, B_433, B_434]: (v4_relat_1(k2_zfmisc_1(k1_relat_1(A_432), B_433), B_434) | ~r1_tarski(k1_relat_1(A_432), B_434) | ~v1_relat_1(A_432) | ~r1_tarski(A_432, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4356, c_2472])).
% 14.17/6.14  tff(c_2556, plain, (![A_329, B_330]: (m1_subset_1(k2_zfmisc_1(A_329, B_330), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(k2_zfmisc_1(A_329, B_330)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2441])).
% 14.17/6.14  tff(c_2559, plain, (![A_329, B_330]: (m1_subset_1(k2_zfmisc_1(A_329, B_330), k1_zfmisc_1(k1_xboole_0)) | ~v4_relat_1(k2_zfmisc_1(A_329, B_330), k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_329, B_330)))), inference(resolution, [status(thm)], [c_46, c_2556])).
% 14.17/6.14  tff(c_2568, plain, (![A_329, B_330]: (m1_subset_1(k2_zfmisc_1(A_329, B_330), k1_zfmisc_1(k1_xboole_0)) | ~v4_relat_1(k2_zfmisc_1(A_329, B_330), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_2559])).
% 14.17/6.14  tff(c_1713, plain, (![D_255, B_256, B_257]: (m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(B_256, B_257))) | ~r1_tarski(k1_relat_1(D_255), B_256) | ~m1_subset_1(D_255, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_678])).
% 14.17/6.14  tff(c_1742, plain, (![D_258, B_259, B_260]: (r1_tarski(D_258, k2_zfmisc_1(B_259, B_260)) | ~r1_tarski(k1_relat_1(D_258), B_259) | ~m1_subset_1(D_258, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1713, c_40])).
% 14.17/6.14  tff(c_1762, plain, (![D_261, B_262]: (r1_tarski(D_261, k2_zfmisc_1(k1_relat_1(D_261), B_262)) | ~m1_subset_1(D_261, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_1742])).
% 14.17/6.14  tff(c_2934, plain, (![D_365, B_366]: (k2_zfmisc_1(k1_relat_1(D_365), B_366)=D_365 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(D_365), B_366), D_365) | ~m1_subset_1(D_365, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_1762, c_2])).
% 14.17/6.14  tff(c_2959, plain, (![D_365]: (k2_zfmisc_1(k1_relat_1(D_365), k1_xboole_0)=D_365 | ~r1_tarski(k1_xboole_0, D_365) | ~m1_subset_1(D_365, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2934])).
% 14.17/6.14  tff(c_2975, plain, (![D_367]: (k1_xboole_0=D_367 | ~m1_subset_1(D_367, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18, c_2959])).
% 14.17/6.14  tff(c_2986, plain, (![A_329, B_330]: (k2_zfmisc_1(A_329, B_330)=k1_xboole_0 | ~v4_relat_1(k2_zfmisc_1(A_329, B_330), k1_xboole_0))), inference(resolution, [status(thm)], [c_2568, c_2975])).
% 14.17/6.14  tff(c_4989, plain, (![A_435, B_436]: (k2_zfmisc_1(k1_relat_1(A_435), B_436)=k1_xboole_0 | ~r1_tarski(k1_relat_1(A_435), k1_xboole_0) | ~v1_relat_1(A_435) | ~r1_tarski(A_435, k1_xboole_0))), inference(resolution, [status(thm)], [c_4891, c_2986])).
% 14.17/6.14  tff(c_5022, plain, (![B_437, B_438]: (k2_zfmisc_1(k1_relat_1(B_437), B_438)=k1_xboole_0 | ~r1_tarski(B_437, k1_xboole_0) | ~v4_relat_1(B_437, k1_xboole_0) | ~v1_relat_1(B_437))), inference(resolution, [status(thm)], [c_46, c_4989])).
% 14.17/6.14  tff(c_2223, plain, (![A_304, B_305, B_306]: (m1_subset_1(A_304, k1_zfmisc_1(k2_zfmisc_1(B_305, B_306))) | ~r1_tarski(k1_relat_1(A_304), B_305) | ~r1_tarski(A_304, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2111])).
% 14.17/6.14  tff(c_2252, plain, (![A_307, B_308, B_309]: (r1_tarski(A_307, k2_zfmisc_1(B_308, B_309)) | ~r1_tarski(k1_relat_1(A_307), B_308) | ~r1_tarski(A_307, k1_xboole_0))), inference(resolution, [status(thm)], [c_2223, c_40])).
% 14.17/6.14  tff(c_2280, plain, (![A_310, B_311]: (r1_tarski(A_310, k2_zfmisc_1(k1_relat_1(A_310), B_311)) | ~r1_tarski(A_310, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_2252])).
% 14.17/6.14  tff(c_2340, plain, (![A_310, B_311]: (k2_zfmisc_1(k1_relat_1(A_310), B_311)=A_310 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_310), B_311), A_310) | ~r1_tarski(A_310, k1_xboole_0))), inference(resolution, [status(thm)], [c_2280, c_2])).
% 14.17/6.14  tff(c_5073, plain, (![B_437, B_438]: (k2_zfmisc_1(k1_relat_1(B_437), B_438)=B_437 | ~r1_tarski(k1_xboole_0, B_437) | ~r1_tarski(B_437, k1_xboole_0) | ~r1_tarski(B_437, k1_xboole_0) | ~v4_relat_1(B_437, k1_xboole_0) | ~v1_relat_1(B_437))), inference(superposition, [status(thm), theory('equality')], [c_5022, c_2340])).
% 14.17/6.14  tff(c_5474, plain, (![B_444, B_445]: (k2_zfmisc_1(k1_relat_1(B_444), B_445)=B_444 | ~r1_tarski(B_444, k1_xboole_0) | ~v4_relat_1(B_444, k1_xboole_0) | ~v1_relat_1(B_444))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5073])).
% 14.17/6.14  tff(c_332, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.17/6.14  tff(c_346, plain, (![A_16, B_97, A_98]: (v5_relat_1(A_16, B_97) | ~r1_tarski(A_16, k2_zfmisc_1(A_98, B_97)))), inference(resolution, [status(thm)], [c_42, c_332])).
% 14.17/6.14  tff(c_6751, plain, (![A_467, B_468, B_469]: (v5_relat_1(A_467, B_468) | ~r1_tarski(A_467, B_469) | ~r1_tarski(B_469, k1_xboole_0) | ~v4_relat_1(B_469, k1_xboole_0) | ~v1_relat_1(B_469))), inference(superposition, [status(thm), theory('equality')], [c_5474, c_346])).
% 14.17/6.14  tff(c_6785, plain, (![B_468]: (v5_relat_1('#skF_4', B_468) | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0) | ~v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(resolution, [status(thm)], [c_820, c_6751])).
% 14.17/6.14  tff(c_6850, plain, (![B_468]: (v5_relat_1('#skF_4', B_468) | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0) | ~v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_6785])).
% 14.17/6.14  tff(c_7364, plain, (~v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_6850])).
% 14.17/6.14  tff(c_7390, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0)), inference(resolution, [status(thm)], [c_404, c_7364])).
% 14.17/6.14  tff(c_10596, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10593, c_7390])).
% 14.17/6.14  tff(c_10615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_10596])).
% 14.17/6.14  tff(c_10617, plain, (v4_relat_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_6850])).
% 14.17/6.14  tff(c_10635, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_10617, c_2986])).
% 14.17/6.14  tff(c_838, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_820, c_2])).
% 14.17/6.14  tff(c_1124, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_838])).
% 14.17/6.14  tff(c_10647, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10635, c_1124])).
% 14.17/6.14  tff(c_10652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_10647])).
% 14.17/6.14  tff(c_10653, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_838])).
% 14.17/6.14  tff(c_62, plain, (![D_38, B_36, C_37, A_35]: (m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(B_36, C_37))) | ~r1_tarski(k1_relat_1(D_38), B_36) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_35, C_37))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.17/6.14  tff(c_11849, plain, (![D_658, B_659]: (m1_subset_1(D_658, k1_zfmisc_1(k2_zfmisc_1(B_659, '#skF_2'))) | ~r1_tarski(k1_relat_1(D_658), B_659) | ~m1_subset_1(D_658, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10653, c_62])).
% 14.17/6.14  tff(c_11937, plain, (![D_663]: (m1_subset_1(D_663, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(D_663), k1_xboole_0) | ~m1_subset_1(D_663, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_20, c_11849])).
% 14.17/6.14  tff(c_11952, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_525, c_11937])).
% 14.17/6.14  tff(c_11966, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11952])).
% 14.17/6.14  tff(c_11976, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11966])).
% 14.17/6.14  tff(c_11979, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_42, c_11976])).
% 14.17/6.14  tff(c_11983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_11979])).
% 14.17/6.14  tff(c_11984, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_11966])).
% 14.17/6.14  tff(c_15427, plain, (![A_814, B_815, D_816]: (k2_tarski(A_814, B_815)=D_816 | k2_tarski(A_814, B_815)=D_816 | k2_tarski(A_814, B_815)=D_816 | k1_tarski(A_814)=D_816 | k1_tarski(B_815)=D_816 | k1_tarski(A_814)=D_816 | k1_tarski(A_814)=D_816 | k1_xboole_0=D_816 | ~r1_tarski(D_816, k2_tarski(A_814, B_815)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_781])).
% 14.17/6.14  tff(c_15440, plain, (![A_4, D_816]: (k2_tarski(A_4, A_4)=D_816 | k2_tarski(A_4, A_4)=D_816 | k2_tarski(A_4, A_4)=D_816 | k1_tarski(A_4)=D_816 | k1_tarski(A_4)=D_816 | k1_tarski(A_4)=D_816 | k1_tarski(A_4)=D_816 | k1_xboole_0=D_816 | ~r1_tarski(D_816, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15427])).
% 14.17/6.14  tff(c_29371, plain, (![A_1085, D_1086]: (k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_tarski(A_1085)=D_1086 | k1_xboole_0=D_1086 | ~r1_tarski(D_1086, k1_tarski(A_1085)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_15440])).
% 14.17/6.14  tff(c_32461, plain, (![A_1123, B_1124]: (k1_tarski(A_1123)=k1_relat_1(B_1124) | k1_relat_1(B_1124)=k1_xboole_0 | ~v4_relat_1(B_1124, k1_tarski(A_1123)) | ~v1_relat_1(B_1124))), inference(resolution, [status(thm)], [c_46, c_29371])).
% 14.17/6.14  tff(c_32527, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_370, c_32461])).
% 14.17/6.14  tff(c_32561, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_32527])).
% 14.17/6.14  tff(c_32562, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_500, c_32561])).
% 14.17/6.14  tff(c_12233, plain, (![D_676, B_677, B_678]: (m1_subset_1(D_676, k1_zfmisc_1(k2_zfmisc_1(B_677, B_678))) | ~r1_tarski(k1_relat_1(D_676), B_677) | ~m1_subset_1(D_676, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_678])).
% 14.17/6.14  tff(c_12323, plain, (![D_681, B_682, B_683]: (r1_tarski(D_681, k2_zfmisc_1(B_682, B_683)) | ~r1_tarski(k1_relat_1(D_681), B_682) | ~m1_subset_1(D_681, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12233, c_40])).
% 14.17/6.14  tff(c_12355, plain, (![D_684, B_685]: (r1_tarski(D_684, k2_zfmisc_1(k1_relat_1(D_684), B_685)) | ~m1_subset_1(D_684, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_12323])).
% 14.17/6.14  tff(c_726, plain, (![B_157]: (v4_relat_1('#skF_4', B_157) | ~r1_tarski(k1_relat_1('#skF_4'), B_157))), inference(resolution, [status(thm)], [c_703, c_58])).
% 14.17/6.14  tff(c_12422, plain, (![B_685]: (v4_relat_1('#skF_4', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')), B_685)) | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_12355, c_726])).
% 14.17/6.14  tff(c_12435, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_12422])).
% 14.17/6.14  tff(c_32584, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32562, c_12435])).
% 14.17/6.14  tff(c_32619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11984, c_32584])).
% 14.17/6.14  tff(c_32621, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_12422])).
% 14.17/6.14  tff(c_32635, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_32621, c_40])).
% 14.17/6.14  tff(c_32644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_745, c_32635])).
% 14.17/6.14  tff(c_32645, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_723])).
% 14.17/6.14  tff(c_32661, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_32645, c_40])).
% 14.17/6.14  tff(c_32715, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32661, c_228])).
% 14.17/6.14  tff(c_32742, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_32715, c_8])).
% 14.17/6.14  tff(c_50, plain, (![A_22]: (k9_relat_1(k1_xboole_0, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.17/6.14  tff(c_32741, plain, (![A_22]: (k9_relat_1('#skF_4', A_22)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32715, c_32715, c_50])).
% 14.17/6.14  tff(c_550, plain, (![A_129, B_130, C_131, D_132]: (k7_relset_1(A_129, B_130, C_131, D_132)=k9_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.17/6.14  tff(c_561, plain, (![D_132]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_132)=k9_relat_1('#skF_4', D_132))), inference(resolution, [status(thm)], [c_68, c_550])).
% 14.17/6.14  tff(c_588, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_561, c_64])).
% 14.17/6.14  tff(c_32881, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32741, c_588])).
% 14.17/6.14  tff(c_32885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32742, c_32881])).
% 14.17/6.14  tff(c_32887, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_461])).
% 14.17/6.14  tff(c_32892, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32887, c_68])).
% 14.17/6.14  tff(c_60, plain, (![A_31, B_32, C_33, D_34]: (k7_relset_1(A_31, B_32, C_33, D_34)=k9_relat_1(C_33, D_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.17/6.14  tff(c_33005, plain, (![D_34]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_34)=k9_relat_1('#skF_4', D_34))), inference(resolution, [status(thm)], [c_32892, c_60])).
% 14.17/6.14  tff(c_32886, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_461])).
% 14.17/6.14  tff(c_33161, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32887, c_32886])).
% 14.17/6.14  tff(c_33162, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_33005, c_33161])).
% 14.17/6.14  tff(c_33242, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_33162])).
% 14.17/6.14  tff(c_33246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_33242])).
% 14.17/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.17/6.14  
% 14.17/6.14  Inference rules
% 14.17/6.14  ----------------------
% 14.17/6.14  #Ref     : 0
% 14.17/6.14  #Sup     : 7249
% 14.17/6.14  #Fact    : 0
% 14.17/6.14  #Define  : 0
% 14.17/6.14  #Split   : 21
% 14.17/6.14  #Chain   : 0
% 14.17/6.14  #Close   : 0
% 14.17/6.14  
% 14.17/6.14  Ordering : KBO
% 14.17/6.14  
% 14.17/6.14  Simplification rules
% 14.17/6.14  ----------------------
% 14.17/6.14  #Subsume      : 2314
% 14.17/6.14  #Demod        : 8719
% 14.17/6.14  #Tautology    : 2497
% 14.17/6.14  #SimpNegUnit  : 35
% 14.17/6.14  #BackRed      : 99
% 14.17/6.14  
% 14.17/6.14  #Partial instantiations: 0
% 14.17/6.14  #Strategies tried      : 1
% 14.17/6.14  
% 14.17/6.14  Timing (in seconds)
% 14.17/6.14  ----------------------
% 14.17/6.14  Preprocessing        : 0.32
% 14.17/6.14  Parsing              : 0.17
% 14.17/6.14  CNF conversion       : 0.02
% 14.17/6.14  Main loop            : 5.04
% 14.17/6.14  Inferencing          : 1.05
% 14.17/6.14  Reduction            : 2.03
% 14.17/6.14  Demodulation         : 1.60
% 14.17/6.14  BG Simplification    : 0.11
% 14.17/6.14  Subsumption          : 1.61
% 14.17/6.14  Abstraction          : 0.18
% 14.17/6.14  MUC search           : 0.00
% 14.17/6.14  Cooper               : 0.00
% 14.17/6.14  Total                : 5.42
% 14.17/6.14  Index Insertion      : 0.00
% 14.17/6.14  Index Deletion       : 0.00
% 14.17/6.14  Index Matching       : 0.00
% 14.17/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
