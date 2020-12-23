%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  144 (1369 expanded)
%              Number of leaves         :   29 ( 454 expanded)
%              Depth                    :   18
%              Number of atoms          :  261 (3209 expanded)
%              Number of equality atoms :   58 ( 751 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_54,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4248,plain,(
    ! [C_446,A_447,B_448] :
      ( m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448)))
      | ~ r1_tarski(k2_relat_1(C_446),B_448)
      | ~ r1_tarski(k1_relat_1(C_446),A_447)
      | ~ v1_relat_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1776,plain,(
    ! [C_218,A_219,B_220] :
      ( v4_relat_1(C_218,A_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1790,plain,(
    ! [C_222,A_223] :
      ( v4_relat_1(C_222,A_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1776])).

tff(c_1795,plain,(
    ! [A_224,A_225] :
      ( v4_relat_1(A_224,A_225)
      | ~ r1_tarski(A_224,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_1790])).

tff(c_72,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_22])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1722,plain,(
    ! [B_210,A_211] :
      ( r1_tarski(k1_relat_1(B_210),A_211)
      | ~ v4_relat_1(B_210,A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1730,plain,(
    ! [A_211] :
      ( r1_tarski(k1_xboole_0,A_211)
      | ~ v4_relat_1(k1_xboole_0,A_211)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1722])).

tff(c_1734,plain,(
    ! [A_211] :
      ( r1_tarski(k1_xboole_0,A_211)
      | ~ v4_relat_1(k1_xboole_0,A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1730])).

tff(c_1799,plain,(
    ! [A_225] :
      ( r1_tarski(k1_xboole_0,A_225)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1795,c_1734])).

tff(c_1802,plain,(
    ! [A_225] : r1_tarski(k1_xboole_0,A_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1799])).

tff(c_52,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_81,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_402,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ r1_tarski(k2_relat_1(C_81),B_83)
      | ~ r1_tarski(k1_relat_1(C_81),A_82)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1195,plain,(
    ! [C_174,A_175,B_176] :
      ( r1_tarski(C_174,k2_zfmisc_1(A_175,B_176))
      | ~ r1_tarski(k2_relat_1(C_174),B_176)
      | ~ r1_tarski(k1_relat_1(C_174),A_175)
      | ~ v1_relat_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_402,c_14])).

tff(c_1197,plain,(
    ! [A_175] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_175,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_175)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1195])).

tff(c_1209,plain,(
    ! [A_177] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_177,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1197])).

tff(c_1229,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1209])).

tff(c_269,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_280,plain,(
    ! [A_61,B_62,A_5] :
      ( k1_relset_1(A_61,B_62,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_16,c_269])).

tff(c_1241,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1229,c_280])).

tff(c_543,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_xboole_0 = B_101
      | v1_funct_2(C_102,A_103,B_101)
      | k1_relset_1(A_103,B_101,C_102) != A_103
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1495,plain,(
    ! [B_194,A_195,A_196] :
      ( k1_xboole_0 = B_194
      | v1_funct_2(A_195,A_196,B_194)
      | k1_relset_1(A_196,B_194,A_195) != A_196
      | ~ r1_tarski(A_195,k2_zfmisc_1(A_196,B_194)) ) ),
    inference(resolution,[status(thm)],[c_16,c_543])).

tff(c_1504,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1229,c_1495])).

tff(c_1527,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1504])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1527])).

tff(c_140,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [C_46,A_47] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_162,plain,(
    ! [A_5,A_47] :
      ( v4_relat_1(A_5,A_47)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_158])).

tff(c_182,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k1_relat_1(B_54),A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [A_55] :
      ( r1_tarski(k1_xboole_0,A_55)
      | ~ v4_relat_1(k1_xboole_0,A_55)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_182])).

tff(c_195,plain,(
    ! [A_56] :
      ( r1_tarski(k1_xboole_0,A_56)
      | ~ v4_relat_1(k1_xboole_0,A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_190])).

tff(c_209,plain,(
    ! [A_47] :
      ( r1_tarski(k1_xboole_0,A_47)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_162,c_195])).

tff(c_218,plain,(
    ! [A_47] : r1_tarski(k1_xboole_0,A_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_209])).

tff(c_1584,plain,(
    ! [A_47] : r1_tarski('#skF_1',A_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_218])).

tff(c_117,plain,(
    ! [B_34,A_35] :
      ( B_34 = A_35
      | ~ r1_tarski(B_34,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_1676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_127])).

tff(c_1677,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1953,plain,(
    ! [C_243,A_244,B_245] :
      ( m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ r1_tarski(k2_relat_1(C_243),B_245)
      | ~ r1_tarski(k1_relat_1(C_243),A_244)
      | ~ v1_relat_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2604,plain,(
    ! [C_328,A_329,B_330] :
      ( r1_tarski(C_328,k2_zfmisc_1(A_329,B_330))
      | ~ r1_tarski(k2_relat_1(C_328),B_330)
      | ~ r1_tarski(k1_relat_1(C_328),A_329)
      | ~ v1_relat_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_1953,c_14])).

tff(c_2687,plain,(
    ! [C_335,A_336] :
      ( r1_tarski(C_335,k2_zfmisc_1(A_336,k2_relat_1(C_335)))
      | ~ r1_tarski(k1_relat_1(C_335),A_336)
      | ~ v1_relat_1(C_335) ) ),
    inference(resolution,[status(thm)],[c_6,c_2604])).

tff(c_2711,plain,(
    ! [A_336] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_336,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_336)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_2687])).

tff(c_2730,plain,(
    ! [A_337] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_337,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2711])).

tff(c_2747,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_2730])).

tff(c_1830,plain,(
    ! [A_229,B_230,C_231] :
      ( k1_relset_1(A_229,B_230,C_231) = k1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1841,plain,(
    ! [A_229,B_230,A_5] :
      ( k1_relset_1(A_229,B_230,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_229,B_230)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1830])).

tff(c_2759,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2747,c_1841])).

tff(c_2261,plain,(
    ! [B_285,C_286,A_287] :
      ( k1_xboole_0 = B_285
      | v1_funct_2(C_286,A_287,B_285)
      | k1_relset_1(A_287,B_285,C_286) != A_287
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_287,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3203,plain,(
    ! [B_366,A_367,A_368] :
      ( k1_xboole_0 = B_366
      | v1_funct_2(A_367,A_368,B_366)
      | k1_relset_1(A_368,B_366,A_367) != A_368
      | ~ r1_tarski(A_367,k2_zfmisc_1(A_368,B_366)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2261])).

tff(c_3215,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2747,c_3203])).

tff(c_3242,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2759,c_3215])).

tff(c_3243,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3242])).

tff(c_2380,plain,(
    ! [C_307,A_308] :
      ( m1_subset_1(C_307,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_307),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_307),A_308)
      | ~ v1_relat_1(C_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1953])).

tff(c_2382,plain,(
    ! [A_308] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_308)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_2380])).

tff(c_2386,plain,(
    ! [A_308] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2382])).

tff(c_2405,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2386])).

tff(c_3270,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3243,c_2405])).

tff(c_3310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3270])).

tff(c_3312,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2386])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3324,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_3312,c_2])).

tff(c_3331,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_3324])).

tff(c_36,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_36])).

tff(c_1816,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_1821,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_1816])).

tff(c_1825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1821])).

tff(c_1827,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1976,plain,(
    ! [B_246,C_247] :
      ( k1_relset_1(k1_xboole_0,B_246,C_247) = k1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1830])).

tff(c_1978,plain,(
    ! [B_246] : k1_relset_1(k1_xboole_0,B_246,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1827,c_1976])).

tff(c_1983,plain,(
    ! [B_246] : k1_relset_1(k1_xboole_0,B_246,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1978])).

tff(c_40,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2031,plain,(
    ! [C_254,B_255] :
      ( v1_funct_2(C_254,k1_xboole_0,B_255)
      | k1_relset_1(k1_xboole_0,B_255,C_254) != k1_xboole_0
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_2033,plain,(
    ! [B_255] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_255)
      | k1_relset_1(k1_xboole_0,B_255,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1827,c_2031])).

tff(c_2039,plain,(
    ! [B_255] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_2033])).

tff(c_3346,plain,(
    ! [B_255] : v1_funct_2('#skF_1','#skF_1',B_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_3331,c_2039])).

tff(c_3368,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_3331,c_26])).

tff(c_3358,plain,(
    ! [A_225] : r1_tarski('#skF_1',A_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_1802])).

tff(c_3311,plain,(
    ! [A_308] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_308)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_2386])).

tff(c_3375,plain,(
    ! [A_308] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_308)
      | m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_3311])).

tff(c_3493,plain,(
    ! [A_378] : ~ r1_tarski(k1_relat_1('#skF_2'),A_378) ),
    inference(splitLeft,[status(thm)],[c_3375])).

tff(c_3505,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_3493])).

tff(c_3506,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3375])).

tff(c_3679,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3506,c_14])).

tff(c_3692,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3679,c_2])).

tff(c_3695,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_3692])).

tff(c_1968,plain,(
    ! [C_243,B_4] :
      ( m1_subset_1(C_243,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_243),B_4)
      | ~ r1_tarski(k1_relat_1(C_243),k1_xboole_0)
      | ~ v1_relat_1(C_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1953])).

tff(c_3535,plain,(
    ! [C_380,B_381] :
      ( m1_subset_1(C_380,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(C_380),B_381)
      | ~ r1_tarski(k1_relat_1(C_380),'#skF_1')
      | ~ v1_relat_1(C_380) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_3331,c_1968])).

tff(c_3538,plain,(
    ! [B_381] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski('#skF_1',B_381)
      | ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_3535])).

tff(c_3543,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3358,c_3538])).

tff(c_3572,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3543])).

tff(c_3798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3368,c_3695,c_3572])).

tff(c_3799,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3543])).

tff(c_3822,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3799,c_14])).

tff(c_3843,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3822,c_2])).

tff(c_3846,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_3843])).

tff(c_3851,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3846,c_3846,c_81])).

tff(c_3857,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3368,c_3851])).

tff(c_3998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3346,c_3857])).

tff(c_3999,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4260,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4248,c_3999])).

tff(c_4276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_50,c_4260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.71  
% 7.53/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.57/2.71  
% 7.57/2.71  %Foreground sorts:
% 7.57/2.71  
% 7.57/2.71  
% 7.57/2.71  %Background operators:
% 7.57/2.71  
% 7.57/2.71  
% 7.57/2.71  %Foreground operators:
% 7.57/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.57/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.57/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.57/2.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.57/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.57/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.57/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.57/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.57/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.57/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.71  
% 7.57/2.75  tff(f_101, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 7.57/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.57/2.75  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.57/2.75  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.57/2.75  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.57/2.75  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.57/2.75  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.57/2.75  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.57/2.75  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.57/2.75  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.57/2.75  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.57/2.75  tff(c_54, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.57/2.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.75  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.57/2.75  tff(c_4248, plain, (![C_446, A_447, B_448]: (m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))) | ~r1_tarski(k2_relat_1(C_446), B_448) | ~r1_tarski(k1_relat_1(C_446), A_447) | ~v1_relat_1(C_446))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.75  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.57/2.75  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.57/2.75  tff(c_1776, plain, (![C_218, A_219, B_220]: (v4_relat_1(C_218, A_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.57/2.75  tff(c_1790, plain, (![C_222, A_223]: (v4_relat_1(C_222, A_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1776])).
% 7.57/2.75  tff(c_1795, plain, (![A_224, A_225]: (v4_relat_1(A_224, A_225) | ~r1_tarski(A_224, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1790])).
% 7.57/2.75  tff(c_72, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.57/2.75  tff(c_22, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.57/2.75  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_22])).
% 7.57/2.75  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.57/2.75  tff(c_1722, plain, (![B_210, A_211]: (r1_tarski(k1_relat_1(B_210), A_211) | ~v4_relat_1(B_210, A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.57/2.75  tff(c_1730, plain, (![A_211]: (r1_tarski(k1_xboole_0, A_211) | ~v4_relat_1(k1_xboole_0, A_211) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1722])).
% 7.57/2.75  tff(c_1734, plain, (![A_211]: (r1_tarski(k1_xboole_0, A_211) | ~v4_relat_1(k1_xboole_0, A_211))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1730])).
% 7.57/2.75  tff(c_1799, plain, (![A_225]: (r1_tarski(k1_xboole_0, A_225) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1795, c_1734])).
% 7.57/2.75  tff(c_1802, plain, (![A_225]: (r1_tarski(k1_xboole_0, A_225))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1799])).
% 7.57/2.75  tff(c_52, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.57/2.75  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.57/2.75  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 7.57/2.75  tff(c_81, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 7.57/2.75  tff(c_402, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~r1_tarski(k2_relat_1(C_81), B_83) | ~r1_tarski(k1_relat_1(C_81), A_82) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.75  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.57/2.75  tff(c_1195, plain, (![C_174, A_175, B_176]: (r1_tarski(C_174, k2_zfmisc_1(A_175, B_176)) | ~r1_tarski(k2_relat_1(C_174), B_176) | ~r1_tarski(k1_relat_1(C_174), A_175) | ~v1_relat_1(C_174))), inference(resolution, [status(thm)], [c_402, c_14])).
% 7.57/2.75  tff(c_1197, plain, (![A_175]: (r1_tarski('#skF_2', k2_zfmisc_1(A_175, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_175) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1195])).
% 7.57/2.75  tff(c_1209, plain, (![A_177]: (r1_tarski('#skF_2', k2_zfmisc_1(A_177, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_177))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1197])).
% 7.57/2.75  tff(c_1229, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1209])).
% 7.57/2.75  tff(c_269, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.57/2.75  tff(c_280, plain, (![A_61, B_62, A_5]: (k1_relset_1(A_61, B_62, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_61, B_62)))), inference(resolution, [status(thm)], [c_16, c_269])).
% 7.57/2.75  tff(c_1241, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1229, c_280])).
% 7.57/2.75  tff(c_543, plain, (![B_101, C_102, A_103]: (k1_xboole_0=B_101 | v1_funct_2(C_102, A_103, B_101) | k1_relset_1(A_103, B_101, C_102)!=A_103 | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.57/2.75  tff(c_1495, plain, (![B_194, A_195, A_196]: (k1_xboole_0=B_194 | v1_funct_2(A_195, A_196, B_194) | k1_relset_1(A_196, B_194, A_195)!=A_196 | ~r1_tarski(A_195, k2_zfmisc_1(A_196, B_194)))), inference(resolution, [status(thm)], [c_16, c_543])).
% 7.57/2.75  tff(c_1504, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1229, c_1495])).
% 7.57/2.75  tff(c_1527, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1504])).
% 7.57/2.75  tff(c_1528, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_1527])).
% 7.57/2.75  tff(c_140, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.57/2.75  tff(c_158, plain, (![C_46, A_47]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 7.57/2.75  tff(c_162, plain, (![A_5, A_47]: (v4_relat_1(A_5, A_47) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_158])).
% 7.57/2.75  tff(c_182, plain, (![B_54, A_55]: (r1_tarski(k1_relat_1(B_54), A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.57/2.75  tff(c_190, plain, (![A_55]: (r1_tarski(k1_xboole_0, A_55) | ~v4_relat_1(k1_xboole_0, A_55) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_182])).
% 7.57/2.75  tff(c_195, plain, (![A_56]: (r1_tarski(k1_xboole_0, A_56) | ~v4_relat_1(k1_xboole_0, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_190])).
% 7.57/2.75  tff(c_209, plain, (![A_47]: (r1_tarski(k1_xboole_0, A_47) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_162, c_195])).
% 7.57/2.75  tff(c_218, plain, (![A_47]: (r1_tarski(k1_xboole_0, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_209])).
% 7.57/2.75  tff(c_1584, plain, (![A_47]: (r1_tarski('#skF_1', A_47))), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_218])).
% 7.57/2.75  tff(c_117, plain, (![B_34, A_35]: (B_34=A_35 | ~r1_tarski(B_34, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.75  tff(c_122, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_117])).
% 7.57/2.75  tff(c_127, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 7.57/2.75  tff(c_1676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1584, c_127])).
% 7.57/2.75  tff(c_1677, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_122])).
% 7.57/2.75  tff(c_1953, plain, (![C_243, A_244, B_245]: (m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~r1_tarski(k2_relat_1(C_243), B_245) | ~r1_tarski(k1_relat_1(C_243), A_244) | ~v1_relat_1(C_243))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.57/2.75  tff(c_2604, plain, (![C_328, A_329, B_330]: (r1_tarski(C_328, k2_zfmisc_1(A_329, B_330)) | ~r1_tarski(k2_relat_1(C_328), B_330) | ~r1_tarski(k1_relat_1(C_328), A_329) | ~v1_relat_1(C_328))), inference(resolution, [status(thm)], [c_1953, c_14])).
% 7.57/2.75  tff(c_2687, plain, (![C_335, A_336]: (r1_tarski(C_335, k2_zfmisc_1(A_336, k2_relat_1(C_335))) | ~r1_tarski(k1_relat_1(C_335), A_336) | ~v1_relat_1(C_335))), inference(resolution, [status(thm)], [c_6, c_2604])).
% 7.57/2.75  tff(c_2711, plain, (![A_336]: (r1_tarski('#skF_2', k2_zfmisc_1(A_336, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_336) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_2687])).
% 7.57/2.75  tff(c_2730, plain, (![A_337]: (r1_tarski('#skF_2', k2_zfmisc_1(A_337, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_337))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2711])).
% 7.57/2.75  tff(c_2747, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_2730])).
% 7.57/2.75  tff(c_1830, plain, (![A_229, B_230, C_231]: (k1_relset_1(A_229, B_230, C_231)=k1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.57/2.75  tff(c_1841, plain, (![A_229, B_230, A_5]: (k1_relset_1(A_229, B_230, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_229, B_230)))), inference(resolution, [status(thm)], [c_16, c_1830])).
% 7.57/2.75  tff(c_2759, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2747, c_1841])).
% 7.57/2.75  tff(c_2261, plain, (![B_285, C_286, A_287]: (k1_xboole_0=B_285 | v1_funct_2(C_286, A_287, B_285) | k1_relset_1(A_287, B_285, C_286)!=A_287 | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_287, B_285))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.57/2.75  tff(c_3203, plain, (![B_366, A_367, A_368]: (k1_xboole_0=B_366 | v1_funct_2(A_367, A_368, B_366) | k1_relset_1(A_368, B_366, A_367)!=A_368 | ~r1_tarski(A_367, k2_zfmisc_1(A_368, B_366)))), inference(resolution, [status(thm)], [c_16, c_2261])).
% 7.57/2.75  tff(c_3215, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2747, c_3203])).
% 7.57/2.75  tff(c_3242, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2759, c_3215])).
% 7.57/2.75  tff(c_3243, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_3242])).
% 7.57/2.75  tff(c_2380, plain, (![C_307, A_308]: (m1_subset_1(C_307, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_307), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_307), A_308) | ~v1_relat_1(C_307))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1953])).
% 7.57/2.75  tff(c_2382, plain, (![A_308]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_308) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_2380])).
% 7.57/2.75  tff(c_2386, plain, (![A_308]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_308))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2382])).
% 7.57/2.75  tff(c_2405, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2386])).
% 7.57/2.75  tff(c_3270, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3243, c_2405])).
% 7.57/2.75  tff(c_3310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3270])).
% 7.57/2.75  tff(c_3312, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2386])).
% 7.57/2.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.75  tff(c_3324, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_3312, c_2])).
% 7.57/2.75  tff(c_3331, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1802, c_3324])).
% 7.57/2.75  tff(c_36, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.57/2.75  tff(c_60, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_36])).
% 7.57/2.75  tff(c_1816, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60])).
% 7.57/2.75  tff(c_1821, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1816])).
% 7.57/2.75  tff(c_1825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1821])).
% 7.57/2.75  tff(c_1827, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_60])).
% 7.57/2.75  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.57/2.75  tff(c_1976, plain, (![B_246, C_247]: (k1_relset_1(k1_xboole_0, B_246, C_247)=k1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1830])).
% 7.57/2.75  tff(c_1978, plain, (![B_246]: (k1_relset_1(k1_xboole_0, B_246, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1827, c_1976])).
% 7.57/2.75  tff(c_1983, plain, (![B_246]: (k1_relset_1(k1_xboole_0, B_246, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1978])).
% 7.57/2.75  tff(c_40, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.57/2.75  tff(c_2031, plain, (![C_254, B_255]: (v1_funct_2(C_254, k1_xboole_0, B_255) | k1_relset_1(k1_xboole_0, B_255, C_254)!=k1_xboole_0 | ~m1_subset_1(C_254, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 7.57/2.75  tff(c_2033, plain, (![B_255]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_255) | k1_relset_1(k1_xboole_0, B_255, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1827, c_2031])).
% 7.57/2.75  tff(c_2039, plain, (![B_255]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_255))), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_2033])).
% 7.57/2.75  tff(c_3346, plain, (![B_255]: (v1_funct_2('#skF_1', '#skF_1', B_255))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_3331, c_2039])).
% 7.57/2.75  tff(c_3368, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_3331, c_26])).
% 7.57/2.75  tff(c_3358, plain, (![A_225]: (r1_tarski('#skF_1', A_225))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_1802])).
% 7.57/2.75  tff(c_3311, plain, (![A_308]: (~r1_tarski(k1_relat_1('#skF_2'), A_308) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_2386])).
% 7.57/2.75  tff(c_3375, plain, (![A_308]: (~r1_tarski(k1_relat_1('#skF_2'), A_308) | m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_3311])).
% 7.57/2.75  tff(c_3493, plain, (![A_378]: (~r1_tarski(k1_relat_1('#skF_2'), A_378))), inference(splitLeft, [status(thm)], [c_3375])).
% 7.57/2.75  tff(c_3505, plain, $false, inference(resolution, [status(thm)], [c_6, c_3493])).
% 7.57/2.75  tff(c_3506, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3375])).
% 7.57/2.75  tff(c_3679, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3506, c_14])).
% 7.57/2.75  tff(c_3692, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3679, c_2])).
% 7.57/2.75  tff(c_3695, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_3692])).
% 7.57/2.75  tff(c_1968, plain, (![C_243, B_4]: (m1_subset_1(C_243, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_243), B_4) | ~r1_tarski(k1_relat_1(C_243), k1_xboole_0) | ~v1_relat_1(C_243))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1953])).
% 7.57/2.75  tff(c_3535, plain, (![C_380, B_381]: (m1_subset_1(C_380, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(C_380), B_381) | ~r1_tarski(k1_relat_1(C_380), '#skF_1') | ~v1_relat_1(C_380))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_3331, c_1968])).
% 7.57/2.75  tff(c_3538, plain, (![B_381]: (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_tarski('#skF_1', B_381) | ~r1_tarski(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_3535])).
% 7.57/2.75  tff(c_3543, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3358, c_3538])).
% 7.57/2.75  tff(c_3572, plain, (~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3543])).
% 7.57/2.75  tff(c_3798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3368, c_3695, c_3572])).
% 7.57/2.75  tff(c_3799, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3543])).
% 7.57/2.75  tff(c_3822, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3799, c_14])).
% 7.57/2.75  tff(c_3843, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3822, c_2])).
% 7.57/2.75  tff(c_3846, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_3843])).
% 7.57/2.75  tff(c_3851, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3846, c_3846, c_81])).
% 7.57/2.75  tff(c_3857, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3368, c_3851])).
% 7.57/2.75  tff(c_3998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3346, c_3857])).
% 7.57/2.75  tff(c_3999, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_56])).
% 7.57/2.75  tff(c_4260, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4248, c_3999])).
% 7.57/2.75  tff(c_4276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_50, c_4260])).
% 7.57/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.75  
% 7.57/2.75  Inference rules
% 7.57/2.75  ----------------------
% 7.57/2.75  #Ref     : 0
% 7.57/2.75  #Sup     : 855
% 7.57/2.75  #Fact    : 0
% 7.57/2.75  #Define  : 0
% 7.57/2.75  #Split   : 17
% 7.57/2.75  #Chain   : 0
% 7.57/2.75  #Close   : 0
% 7.57/2.75  
% 7.57/2.75  Ordering : KBO
% 7.57/2.75  
% 7.57/2.75  Simplification rules
% 7.57/2.75  ----------------------
% 7.57/2.75  #Subsume      : 113
% 7.57/2.75  #Demod        : 1212
% 7.57/2.75  #Tautology    : 405
% 7.57/2.75  #SimpNegUnit  : 10
% 7.57/2.75  #BackRed      : 177
% 7.57/2.75  
% 7.57/2.75  #Partial instantiations: 0
% 7.57/2.75  #Strategies tried      : 1
% 7.57/2.75  
% 7.57/2.75  Timing (in seconds)
% 7.57/2.75  ----------------------
% 7.57/2.76  Preprocessing        : 0.37
% 7.57/2.76  Parsing              : 0.18
% 7.57/2.76  CNF conversion       : 0.03
% 7.57/2.76  Main loop            : 1.56
% 7.57/2.76  Inferencing          : 0.56
% 7.57/2.76  Reduction            : 0.50
% 7.57/2.76  Demodulation         : 0.36
% 7.57/2.76  BG Simplification    : 0.05
% 7.57/2.76  Subsumption          : 0.31
% 7.57/2.76  Abstraction          : 0.07
% 7.57/2.76  MUC search           : 0.00
% 7.57/2.76  Cooper               : 0.00
% 7.57/2.76  Total                : 2.01
% 7.57/2.76  Index Insertion      : 0.00
% 7.57/2.76  Index Deletion       : 0.00
% 7.57/2.76  Index Matching       : 0.00
% 7.57/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
