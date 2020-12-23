%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:52 EST 2020

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 142 expanded)
%              Number of leaves         :   48 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 221 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_97,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B = k1_tarski(A)
         => k7_setfam_1(A,B) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_102,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

tff(c_98,plain,(
    ! [A_55] : ~ v1_xboole_0(k1_zfmisc_1(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    ! [A_40] : k1_subset_1(A_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_96,plain,(
    ! [A_54] : m1_subset_1(k1_subset_1(A_54),k1_zfmisc_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_126,plain,(
    ! [A_54] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_96])).

tff(c_110,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,B_66)
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_120,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_34,plain,(
    ! [B_39] : r1_tarski(k1_tarski(B_39),k1_tarski(B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_239,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,B_94)
      | ~ r1_tarski(k1_tarski(A_93),B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [B_39] : r2_hidden(B_39,k1_tarski(B_39)) ),
    inference(resolution,[status(thm)],[c_34,c_239])).

tff(c_102,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tarski(A_57),k1_zfmisc_1(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    ! [A_41] : k2_subset_1(A_41) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_subset_1(A_56)) = k2_subset_1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_125,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_subset_1(A_56)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_100])).

tff(c_127,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_125])).

tff(c_1326,plain,(
    ! [A_340,C_341,B_342] :
      ( r2_hidden(k3_subset_1(A_340,C_341),k7_setfam_1(A_340,B_342))
      | ~ r2_hidden(C_341,B_342)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(A_340))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k1_zfmisc_1(A_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1341,plain,(
    ! [A_56,B_342] :
      ( r2_hidden(A_56,k7_setfam_1(A_56,B_342))
      | ~ r2_hidden(k1_xboole_0,B_342)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1326])).

tff(c_1878,plain,(
    ! [A_605,B_606] :
      ( r2_hidden(A_605,k7_setfam_1(A_605,B_606))
      | ~ r2_hidden(k1_xboole_0,B_606)
      | ~ m1_subset_1(B_606,k1_zfmisc_1(k1_zfmisc_1(A_605))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1341])).

tff(c_2469,plain,(
    ! [A_693,A_694] :
      ( r2_hidden(A_693,k7_setfam_1(A_693,k1_tarski(A_694)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_694))
      | ~ r2_hidden(A_694,k1_zfmisc_1(A_693)) ) ),
    inference(resolution,[status(thm)],[c_102,c_1878])).

tff(c_122,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_234,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_tarski(A_90),B_91)
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_237,plain,(
    ! [B_91] :
      ( r1_tarski('#skF_4',B_91)
      | ~ r2_hidden('#skF_3',B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_234])).

tff(c_2480,plain,(
    ! [A_694] :
      ( r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_694)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_694))
      | ~ r2_hidden(A_694,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2469,c_237])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_321,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_330,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_321])).

tff(c_333,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_330])).

tff(c_251,plain,(
    ! [B_95] : k4_xboole_0(k1_tarski(B_95),k1_tarski(B_95)) != k1_tarski(B_95) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_254,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_251])).

tff(c_258,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_122,c_254])).

tff(c_334,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_258])).

tff(c_124,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_544,plain,(
    ! [A_141,B_142] :
      ( k7_setfam_1(A_141,B_142) != k1_xboole_0
      | k1_xboole_0 = B_142
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k1_zfmisc_1(A_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_555,plain,
    ( k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_544])).

tff(c_571,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_555])).

tff(c_104,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k7_setfam_1(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_707,plain,(
    ! [A_180,B_181] :
      ( k7_setfam_1(A_180,k7_setfam_1(A_180,B_181)) = B_181
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k1_zfmisc_1(A_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_723,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_707])).

tff(c_1408,plain,(
    ! [C_382,B_383,A_384] :
      ( r2_hidden(C_382,B_383)
      | ~ r2_hidden(k3_subset_1(A_384,C_382),k7_setfam_1(A_384,B_383))
      | ~ m1_subset_1(C_382,k1_zfmisc_1(A_384))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(k1_zfmisc_1(A_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1423,plain,(
    ! [C_382] :
      ( r2_hidden(C_382,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_382),'#skF_4')
      | ~ m1_subset_1(C_382,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_1408])).

tff(c_1808,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1811,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_104,c_1808])).

tff(c_1815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1811])).

tff(c_1817,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_1508,plain,(
    ! [B_427,C_428,A_429] :
      ( r1_tarski(B_427,C_428)
      | ~ r1_tarski(k7_setfam_1(A_429,B_427),k7_setfam_1(A_429,C_428))
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k1_zfmisc_1(A_429)))
      | ~ m1_subset_1(B_427,k1_zfmisc_1(k1_zfmisc_1(A_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1529,plain,(
    ! [C_428] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_428)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_428))
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_1508])).

tff(c_2261,plain,(
    ! [C_673] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_673)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_673))
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_1529])).

tff(c_3019,plain,(
    ! [A_759] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k1_tarski(A_759))
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_759)))
      | ~ r2_hidden(A_759,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_102,c_2261])).

tff(c_32,plain,(
    ! [B_39,A_38] :
      ( k1_tarski(B_39) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k1_tarski(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3022,plain,(
    ! [A_759] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_759)
      | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_759)))
      | ~ r2_hidden(A_759,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3019,c_32])).

tff(c_3031,plain,(
    ! [A_760] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_760)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_760)))
      | ~ r2_hidden(A_760,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_571,c_3022])).

tff(c_3044,plain,(
    ! [A_761] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_761)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_761))
      | ~ r2_hidden(A_761,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2480,c_3031])).

tff(c_3050,plain,
    ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_250,c_3044])).

tff(c_3056,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3050])).

tff(c_3060,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_3056])).

tff(c_3063,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_3060])).

tff(c_3065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_3063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.55/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.36  
% 6.55/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.55/2.36  
% 6.55/2.36  %Foreground sorts:
% 6.55/2.36  
% 6.55/2.36  
% 6.55/2.36  %Background operators:
% 6.55/2.36  
% 6.55/2.36  
% 6.55/2.36  %Foreground operators:
% 6.55/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.55/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.55/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.55/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.55/2.36  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 6.55/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.55/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.55/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.55/2.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.55/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.55/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.55/2.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.55/2.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.55/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.55/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.55/2.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.55/2.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.55/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.55/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.55/2.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.55/2.36  
% 6.55/2.37  tff(f_100, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.55/2.37  tff(f_63, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 6.55/2.37  tff(f_97, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 6.55/2.37  tff(f_122, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.55/2.37  tff(f_155, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((B = k1_tarski(A)) => (k7_setfam_1(A, B) = k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_setfam_1)).
% 6.55/2.37  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 6.55/2.37  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 6.55/2.37  tff(f_106, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 6.55/2.37  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.55/2.37  tff(f_102, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 6.55/2.37  tff(f_139, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 6.55/2.37  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.55/2.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.55/2.37  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.55/2.37  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.55/2.37  tff(f_130, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 6.55/2.37  tff(f_110, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 6.55/2.37  tff(f_114, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 6.55/2.37  tff(f_148, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 6.55/2.37  tff(c_98, plain, (![A_55]: (~v1_xboole_0(k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.55/2.37  tff(c_38, plain, (![A_40]: (k1_subset_1(A_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.55/2.37  tff(c_96, plain, (![A_54]: (m1_subset_1(k1_subset_1(A_54), k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.55/2.37  tff(c_126, plain, (![A_54]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_96])).
% 6.55/2.37  tff(c_110, plain, (![A_65, B_66]: (r2_hidden(A_65, B_66) | v1_xboole_0(B_66) | ~m1_subset_1(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.55/2.37  tff(c_120, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.55/2.37  tff(c_34, plain, (![B_39]: (r1_tarski(k1_tarski(B_39), k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.37  tff(c_239, plain, (![A_93, B_94]: (r2_hidden(A_93, B_94) | ~r1_tarski(k1_tarski(A_93), B_94))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.55/2.37  tff(c_250, plain, (![B_39]: (r2_hidden(B_39, k1_tarski(B_39)))), inference(resolution, [status(thm)], [c_34, c_239])).
% 6.55/2.37  tff(c_102, plain, (![A_57, B_58]: (m1_subset_1(k1_tarski(A_57), k1_zfmisc_1(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.55/2.37  tff(c_40, plain, (![A_41]: (k2_subset_1(A_41)=A_41)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.55/2.37  tff(c_100, plain, (![A_56]: (k3_subset_1(A_56, k1_subset_1(A_56))=k2_subset_1(A_56))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.55/2.37  tff(c_125, plain, (![A_56]: (k3_subset_1(A_56, k1_subset_1(A_56))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_100])).
% 6.55/2.38  tff(c_127, plain, (![A_56]: (k3_subset_1(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_125])).
% 6.55/2.38  tff(c_1326, plain, (![A_340, C_341, B_342]: (r2_hidden(k3_subset_1(A_340, C_341), k7_setfam_1(A_340, B_342)) | ~r2_hidden(C_341, B_342) | ~m1_subset_1(C_341, k1_zfmisc_1(A_340)) | ~m1_subset_1(B_342, k1_zfmisc_1(k1_zfmisc_1(A_340))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.55/2.38  tff(c_1341, plain, (![A_56, B_342]: (r2_hidden(A_56, k7_setfam_1(A_56, B_342)) | ~r2_hidden(k1_xboole_0, B_342) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_342, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(superposition, [status(thm), theory('equality')], [c_127, c_1326])).
% 6.55/2.38  tff(c_1878, plain, (![A_605, B_606]: (r2_hidden(A_605, k7_setfam_1(A_605, B_606)) | ~r2_hidden(k1_xboole_0, B_606) | ~m1_subset_1(B_606, k1_zfmisc_1(k1_zfmisc_1(A_605))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1341])).
% 6.55/2.38  tff(c_2469, plain, (![A_693, A_694]: (r2_hidden(A_693, k7_setfam_1(A_693, k1_tarski(A_694))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_694)) | ~r2_hidden(A_694, k1_zfmisc_1(A_693)))), inference(resolution, [status(thm)], [c_102, c_1878])).
% 6.55/2.38  tff(c_122, plain, (k1_tarski('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.55/2.38  tff(c_234, plain, (![A_90, B_91]: (r1_tarski(k1_tarski(A_90), B_91) | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.55/2.38  tff(c_237, plain, (![B_91]: (r1_tarski('#skF_4', B_91) | ~r2_hidden('#skF_3', B_91))), inference(superposition, [status(thm), theory('equality')], [c_122, c_234])).
% 6.55/2.38  tff(c_2480, plain, (![A_694]: (r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_694))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_694)) | ~r2_hidden(A_694, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2469, c_237])).
% 6.55/2.38  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.55/2.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.55/2.38  tff(c_321, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.55/2.38  tff(c_330, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_321])).
% 6.55/2.38  tff(c_333, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_330])).
% 6.55/2.38  tff(c_251, plain, (![B_95]: (k4_xboole_0(k1_tarski(B_95), k1_tarski(B_95))!=k1_tarski(B_95))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.55/2.38  tff(c_254, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_122, c_251])).
% 6.55/2.38  tff(c_258, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_122, c_254])).
% 6.55/2.38  tff(c_334, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_258])).
% 6.55/2.38  tff(c_124, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.55/2.38  tff(c_544, plain, (![A_141, B_142]: (k7_setfam_1(A_141, B_142)!=k1_xboole_0 | k1_xboole_0=B_142 | ~m1_subset_1(B_142, k1_zfmisc_1(k1_zfmisc_1(A_141))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.55/2.38  tff(c_555, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_124, c_544])).
% 6.55/2.38  tff(c_571, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_334, c_555])).
% 6.55/2.38  tff(c_104, plain, (![A_59, B_60]: (m1_subset_1(k7_setfam_1(A_59, B_60), k1_zfmisc_1(k1_zfmisc_1(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.55/2.38  tff(c_707, plain, (![A_180, B_181]: (k7_setfam_1(A_180, k7_setfam_1(A_180, B_181))=B_181 | ~m1_subset_1(B_181, k1_zfmisc_1(k1_zfmisc_1(A_180))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.55/2.38  tff(c_723, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_124, c_707])).
% 6.55/2.38  tff(c_1408, plain, (![C_382, B_383, A_384]: (r2_hidden(C_382, B_383) | ~r2_hidden(k3_subset_1(A_384, C_382), k7_setfam_1(A_384, B_383)) | ~m1_subset_1(C_382, k1_zfmisc_1(A_384)) | ~m1_subset_1(B_383, k1_zfmisc_1(k1_zfmisc_1(A_384))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.55/2.38  tff(c_1423, plain, (![C_382]: (r2_hidden(C_382, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_382), '#skF_4') | ~m1_subset_1(C_382, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_723, c_1408])).
% 6.55/2.38  tff(c_1808, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1423])).
% 6.55/2.38  tff(c_1811, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_104, c_1808])).
% 6.55/2.38  tff(c_1815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_1811])).
% 6.55/2.38  tff(c_1817, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1423])).
% 6.55/2.38  tff(c_1508, plain, (![B_427, C_428, A_429]: (r1_tarski(B_427, C_428) | ~r1_tarski(k7_setfam_1(A_429, B_427), k7_setfam_1(A_429, C_428)) | ~m1_subset_1(C_428, k1_zfmisc_1(k1_zfmisc_1(A_429))) | ~m1_subset_1(B_427, k1_zfmisc_1(k1_zfmisc_1(A_429))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.55/2.38  tff(c_1529, plain, (![C_428]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_428) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_428)) | ~m1_subset_1(C_428, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_723, c_1508])).
% 6.55/2.38  tff(c_2261, plain, (![C_673]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_673) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_673)) | ~m1_subset_1(C_673, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1817, c_1529])).
% 6.55/2.38  tff(c_3019, plain, (![A_759]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), k1_tarski(A_759)) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_759))) | ~r2_hidden(A_759, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_102, c_2261])).
% 6.55/2.38  tff(c_32, plain, (![B_39, A_38]: (k1_tarski(B_39)=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.55/2.38  tff(c_3022, plain, (![A_759]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_759) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_759))) | ~r2_hidden(A_759, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_3019, c_32])).
% 6.55/2.38  tff(c_3031, plain, (![A_760]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_760) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_760))) | ~r2_hidden(A_760, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_571, c_3022])).
% 6.55/2.38  tff(c_3044, plain, (![A_761]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_761) | ~r2_hidden(k1_xboole_0, k1_tarski(A_761)) | ~r2_hidden(A_761, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2480, c_3031])).
% 6.55/2.38  tff(c_3050, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(k1_xboole_0) | ~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_250, c_3044])).
% 6.55/2.38  tff(c_3056, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_120, c_3050])).
% 6.55/2.38  tff(c_3060, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_110, c_3056])).
% 6.55/2.38  tff(c_3063, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_3060])).
% 6.55/2.38  tff(c_3065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_3063])).
% 6.55/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.38  
% 6.55/2.38  Inference rules
% 6.55/2.38  ----------------------
% 6.55/2.38  #Ref     : 0
% 6.55/2.38  #Sup     : 629
% 6.55/2.38  #Fact    : 0
% 6.55/2.38  #Define  : 0
% 6.55/2.38  #Split   : 11
% 6.55/2.38  #Chain   : 0
% 6.55/2.38  #Close   : 0
% 6.55/2.38  
% 6.55/2.38  Ordering : KBO
% 6.55/2.38  
% 6.55/2.38  Simplification rules
% 6.55/2.38  ----------------------
% 6.55/2.38  #Subsume      : 157
% 6.55/2.38  #Demod        : 267
% 6.55/2.38  #Tautology    : 219
% 6.55/2.38  #SimpNegUnit  : 67
% 6.55/2.38  #BackRed      : 8
% 6.55/2.38  
% 6.55/2.38  #Partial instantiations: 0
% 6.55/2.38  #Strategies tried      : 1
% 6.55/2.38  
% 6.55/2.38  Timing (in seconds)
% 6.55/2.38  ----------------------
% 6.55/2.38  Preprocessing        : 0.42
% 6.55/2.38  Parsing              : 0.21
% 6.55/2.38  CNF conversion       : 0.03
% 6.55/2.38  Main loop            : 1.05
% 6.55/2.38  Inferencing          : 0.35
% 6.55/2.38  Reduction            : 0.37
% 6.55/2.38  Demodulation         : 0.26
% 6.55/2.38  BG Simplification    : 0.04
% 6.55/2.38  Subsumption          : 0.23
% 6.55/2.38  Abstraction          : 0.04
% 6.55/2.38  MUC search           : 0.00
% 6.55/2.38  Cooper               : 0.00
% 6.55/2.38  Total                : 1.51
% 6.55/2.38  Index Insertion      : 0.00
% 6.55/2.38  Index Deletion       : 0.00
% 6.55/2.38  Index Matching       : 0.00
% 6.55/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
