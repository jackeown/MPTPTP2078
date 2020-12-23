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
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 380 expanded)
%              Number of leaves         :   44 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  170 ( 711 expanded)
%              Number of equality atoms :   36 ( 125 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_34,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_352,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_355,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_352])).

tff(c_358,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_355])).

tff(c_518,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_527,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_518])).

tff(c_539,plain,(
    ! [B_120,A_121] :
      ( k7_relat_1(B_120,A_121) = B_120
      | ~ v4_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_542,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_527,c_539])).

tff(c_545,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_542])).

tff(c_22,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [B_64,A_65] :
      ( r1_xboole_0(B_64,A_65)
      | ~ r1_xboole_0(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_15] : r1_xboole_0(k1_xboole_0,A_15) ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [B_67,A_68] : r1_tarski(k3_xboole_0(B_67,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_20])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_490,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_728,plain,(
    ! [A_140,B_141,B_142] :
      ( r2_hidden('#skF_1'(A_140,B_141),B_142)
      | ~ r1_tarski(A_140,B_142)
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_8,c_490])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_745,plain,(
    ! [A_140,B_141,B_142] :
      ( m1_subset_1('#skF_1'(A_140,B_141),B_142)
      | ~ r1_tarski(A_140,B_142)
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_728,c_28])).

tff(c_705,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_714,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_705])).

tff(c_50,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_716,plain,(
    ! [D_54] :
      ( ~ r2_hidden(D_54,k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_54,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_50])).

tff(c_794,plain,(
    ! [A_151,B_152] :
      ( ~ m1_subset_1('#skF_1'(A_151,B_152),'#skF_3')
      | ~ r1_tarski(A_151,k1_relat_1('#skF_4'))
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_728,c_716])).

tff(c_804,plain,(
    ! [A_153,B_154] :
      ( ~ r1_tarski(A_153,k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_153,'#skF_3')
      | r1_tarski(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_745,c_794])).

tff(c_856,plain,(
    ! [B_160,B_161] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'),B_160),'#skF_3')
      | r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'),B_160),B_161) ) ),
    inference(resolution,[status(thm)],[c_20,c_804])).

tff(c_862,plain,(
    ! [B_161] : r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3'),B_161) ),
    inference(resolution,[status(thm)],[c_99,c_856])).

tff(c_873,plain,(
    ! [B_162] : r1_tarski(k3_xboole_0('#skF_3',k1_relat_1('#skF_4')),B_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_862])).

tff(c_241,plain,(
    ! [B_89,A_90] :
      ( ~ r1_xboole_0(B_89,A_90)
      | ~ r1_tarski(B_89,A_90)
      | v1_xboole_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_251,plain,(
    ! [A_91] :
      ( ~ r1_tarski(A_91,k1_xboole_0)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_22,c_241])).

tff(c_268,plain,(
    ! [B_92] : v1_xboole_0(k3_xboole_0(B_92,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_99,c_251])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_320,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_359,plain,(
    ! [B_99] : r1_tarski(k1_xboole_0,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_20])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_366,plain,(
    ! [B_99] :
      ( k1_xboole_0 = B_99
      | ~ r1_tarski(B_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_359,c_14])).

tff(c_910,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_873,c_366])).

tff(c_461,plain,(
    ! [A_105,B_106] :
      ( ~ r1_xboole_0(k3_xboole_0(A_105,B_106),B_106)
      | r1_xboole_0(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_470,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_461])).

tff(c_954,plain,
    ( ~ r1_xboole_0(k1_xboole_0,'#skF_3')
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_470])).

tff(c_973,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_954])).

tff(c_40,plain,(
    ! [A_33] :
      ( k7_relat_1(A_33,k1_relat_1(A_33)) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_546,plain,(
    ! [C_122,A_123,B_124] :
      ( k7_relat_1(k7_relat_1(C_122,A_123),B_124) = k1_xboole_0
      | ~ r1_xboole_0(A_123,B_124)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_565,plain,(
    ! [A_33,B_124] :
      ( k7_relat_1(A_33,B_124) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(A_33),B_124)
      | ~ v1_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_981,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_973,c_565])).

tff(c_989,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_545,c_981])).

tff(c_774,plain,(
    ! [A_148,B_149,C_150] :
      ( k2_relset_1(A_148,B_149,C_150) = k2_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_788,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_774])).

tff(c_52,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_789,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_52])).

tff(c_996,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_789])).

tff(c_32,plain,(
    ! [A_25] :
      ( v1_xboole_0(k2_relat_1(A_25))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    ! [A_60] :
      ( v1_xboole_0(k2_relat_1(A_60))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_63] :
      ( k2_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_64,c_10])).

tff(c_134,plain,(
    ! [A_73] :
      ( k2_relat_1(k2_relat_1(A_73)) = k1_xboole_0
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_143,plain,(
    ! [A_73] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k2_relat_1(A_73))
      | ~ v1_xboole_0(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_32])).

tff(c_163,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_relat_1(A_76))
      | ~ v1_xboole_0(A_76) ) ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_170,plain,(
    ! [A_25] : ~ v1_xboole_0(A_25) ),
    inference(resolution,[status(thm)],[c_32,c_163])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_xboole_0(B_17,A_16)
      | ~ r1_tarski(B_17,A_16)
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_195,plain,(
    ! [B_84,A_85] :
      ( ~ r1_xboole_0(B_84,A_85)
      | ~ r1_tarski(B_84,A_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_24])).

tff(c_204,plain,(
    ! [A_86] : ~ r1_tarski(A_86,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_215,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_99,c_204])).

tff(c_216,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_68,plain,(
    ! [A_60] :
      ( k2_relat_1(A_60) = k1_xboole_0
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_64,c_10])).

tff(c_224,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216,c_68])).

tff(c_1006,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_989,c_224])).

tff(c_1104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:59:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.58  
% 3.08/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.08/1.58  
% 3.08/1.58  %Foreground sorts:
% 3.08/1.58  
% 3.08/1.58  
% 3.08/1.58  %Background operators:
% 3.08/1.58  
% 3.08/1.58  
% 3.08/1.58  %Foreground operators:
% 3.08/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.08/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.08/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.08/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.08/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.08/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.58  
% 3.08/1.60  tff(f_83, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.60  tff(f_134, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.08/1.60  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.60  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.08/1.60  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.08/1.60  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.08/1.60  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.08/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.08/1.60  tff(f_50, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.08/1.60  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.08/1.60  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.08/1.60  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.08/1.60  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.08/1.60  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.08/1.60  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.60  tff(f_66, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.08/1.60  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.08/1.60  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 3.08/1.60  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.60  tff(f_81, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.08/1.60  tff(c_34, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.08/1.60  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.60  tff(c_352, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.08/1.60  tff(c_355, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_352])).
% 3.08/1.60  tff(c_358, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_355])).
% 3.08/1.60  tff(c_518, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.60  tff(c_527, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_518])).
% 3.08/1.60  tff(c_539, plain, (![B_120, A_121]: (k7_relat_1(B_120, A_121)=B_120 | ~v4_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.08/1.60  tff(c_542, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_527, c_539])).
% 3.08/1.60  tff(c_545, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_542])).
% 3.08/1.60  tff(c_22, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.60  tff(c_75, plain, (![B_64, A_65]: (r1_xboole_0(B_64, A_65) | ~r1_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.08/1.60  tff(c_78, plain, (![A_15]: (r1_xboole_0(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_22, c_75])).
% 3.08/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.60  tff(c_84, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.60  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.08/1.60  tff(c_99, plain, (![B_67, A_68]: (r1_tarski(k3_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_84, c_20])).
% 3.08/1.60  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.60  tff(c_490, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.60  tff(c_728, plain, (![A_140, B_141, B_142]: (r2_hidden('#skF_1'(A_140, B_141), B_142) | ~r1_tarski(A_140, B_142) | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_8, c_490])).
% 3.08/1.60  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.08/1.60  tff(c_745, plain, (![A_140, B_141, B_142]: (m1_subset_1('#skF_1'(A_140, B_141), B_142) | ~r1_tarski(A_140, B_142) | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_728, c_28])).
% 3.08/1.60  tff(c_705, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.08/1.60  tff(c_714, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_705])).
% 3.08/1.60  tff(c_50, plain, (![D_54]: (~r2_hidden(D_54, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.60  tff(c_716, plain, (![D_54]: (~r2_hidden(D_54, k1_relat_1('#skF_4')) | ~m1_subset_1(D_54, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_50])).
% 3.08/1.60  tff(c_794, plain, (![A_151, B_152]: (~m1_subset_1('#skF_1'(A_151, B_152), '#skF_3') | ~r1_tarski(A_151, k1_relat_1('#skF_4')) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_728, c_716])).
% 3.08/1.60  tff(c_804, plain, (![A_153, B_154]: (~r1_tarski(A_153, k1_relat_1('#skF_4')) | ~r1_tarski(A_153, '#skF_3') | r1_tarski(A_153, B_154))), inference(resolution, [status(thm)], [c_745, c_794])).
% 3.08/1.60  tff(c_856, plain, (![B_160, B_161]: (~r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'), B_160), '#skF_3') | r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'), B_160), B_161))), inference(resolution, [status(thm)], [c_20, c_804])).
% 3.08/1.60  tff(c_862, plain, (![B_161]: (r1_tarski(k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3'), B_161))), inference(resolution, [status(thm)], [c_99, c_856])).
% 3.08/1.60  tff(c_873, plain, (![B_162]: (r1_tarski(k3_xboole_0('#skF_3', k1_relat_1('#skF_4')), B_162))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_862])).
% 3.08/1.60  tff(c_241, plain, (![B_89, A_90]: (~r1_xboole_0(B_89, A_90) | ~r1_tarski(B_89, A_90) | v1_xboole_0(B_89))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.60  tff(c_251, plain, (![A_91]: (~r1_tarski(A_91, k1_xboole_0) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_22, c_241])).
% 3.08/1.60  tff(c_268, plain, (![B_92]: (v1_xboole_0(k3_xboole_0(B_92, k1_xboole_0)))), inference(resolution, [status(thm)], [c_99, c_251])).
% 3.08/1.60  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.60  tff(c_320, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_268, c_10])).
% 3.08/1.60  tff(c_359, plain, (![B_99]: (r1_tarski(k1_xboole_0, B_99))), inference(superposition, [status(thm), theory('equality')], [c_320, c_20])).
% 3.08/1.60  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.08/1.60  tff(c_366, plain, (![B_99]: (k1_xboole_0=B_99 | ~r1_tarski(B_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_359, c_14])).
% 3.08/1.60  tff(c_910, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_873, c_366])).
% 3.08/1.60  tff(c_461, plain, (![A_105, B_106]: (~r1_xboole_0(k3_xboole_0(A_105, B_106), B_106) | r1_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.08/1.60  tff(c_470, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_461])).
% 3.08/1.60  tff(c_954, plain, (~r1_xboole_0(k1_xboole_0, '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_910, c_470])).
% 3.08/1.60  tff(c_973, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_954])).
% 3.08/1.60  tff(c_40, plain, (![A_33]: (k7_relat_1(A_33, k1_relat_1(A_33))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.08/1.60  tff(c_546, plain, (![C_122, A_123, B_124]: (k7_relat_1(k7_relat_1(C_122, A_123), B_124)=k1_xboole_0 | ~r1_xboole_0(A_123, B_124) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.08/1.60  tff(c_565, plain, (![A_33, B_124]: (k7_relat_1(A_33, B_124)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(A_33), B_124) | ~v1_relat_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_40, c_546])).
% 3.08/1.60  tff(c_981, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_973, c_565])).
% 3.08/1.60  tff(c_989, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_545, c_981])).
% 3.08/1.60  tff(c_774, plain, (![A_148, B_149, C_150]: (k2_relset_1(A_148, B_149, C_150)=k2_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.08/1.60  tff(c_788, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_774])).
% 3.08/1.60  tff(c_52, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.08/1.60  tff(c_789, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_788, c_52])).
% 3.08/1.60  tff(c_996, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_989, c_789])).
% 3.08/1.60  tff(c_32, plain, (![A_25]: (v1_xboole_0(k2_relat_1(A_25)) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.60  tff(c_64, plain, (![A_60]: (v1_xboole_0(k2_relat_1(A_60)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.60  tff(c_70, plain, (![A_63]: (k2_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_64, c_10])).
% 3.08/1.60  tff(c_134, plain, (![A_73]: (k2_relat_1(k2_relat_1(A_73))=k1_xboole_0 | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_32, c_70])).
% 3.08/1.60  tff(c_143, plain, (![A_73]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k2_relat_1(A_73)) | ~v1_xboole_0(A_73))), inference(superposition, [status(thm), theory('equality')], [c_134, c_32])).
% 3.08/1.60  tff(c_163, plain, (![A_76]: (~v1_xboole_0(k2_relat_1(A_76)) | ~v1_xboole_0(A_76))), inference(splitLeft, [status(thm)], [c_143])).
% 3.08/1.60  tff(c_170, plain, (![A_25]: (~v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_32, c_163])).
% 3.08/1.60  tff(c_24, plain, (![B_17, A_16]: (~r1_xboole_0(B_17, A_16) | ~r1_tarski(B_17, A_16) | v1_xboole_0(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.60  tff(c_195, plain, (![B_84, A_85]: (~r1_xboole_0(B_84, A_85) | ~r1_tarski(B_84, A_85))), inference(negUnitSimplification, [status(thm)], [c_170, c_24])).
% 3.08/1.60  tff(c_204, plain, (![A_86]: (~r1_tarski(A_86, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_195])).
% 3.08/1.60  tff(c_215, plain, $false, inference(resolution, [status(thm)], [c_99, c_204])).
% 3.08/1.60  tff(c_216, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_143])).
% 3.08/1.60  tff(c_68, plain, (![A_60]: (k2_relat_1(A_60)=k1_xboole_0 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_64, c_10])).
% 3.08/1.60  tff(c_224, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_216, c_68])).
% 3.08/1.60  tff(c_1006, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_989, c_989, c_224])).
% 3.08/1.60  tff(c_1104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_1006])).
% 3.08/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.60  
% 3.08/1.60  Inference rules
% 3.08/1.60  ----------------------
% 3.08/1.60  #Ref     : 0
% 3.08/1.60  #Sup     : 224
% 3.08/1.60  #Fact    : 0
% 3.08/1.60  #Define  : 0
% 3.08/1.60  #Split   : 3
% 3.08/1.60  #Chain   : 0
% 3.08/1.60  #Close   : 0
% 3.08/1.60  
% 3.08/1.60  Ordering : KBO
% 3.08/1.60  
% 3.08/1.60  Simplification rules
% 3.08/1.60  ----------------------
% 3.08/1.60  #Subsume      : 30
% 3.08/1.60  #Demod        : 157
% 3.08/1.60  #Tautology    : 115
% 3.08/1.60  #SimpNegUnit  : 3
% 3.08/1.60  #BackRed      : 27
% 3.08/1.60  
% 3.08/1.60  #Partial instantiations: 0
% 3.08/1.60  #Strategies tried      : 1
% 3.08/1.60  
% 3.08/1.60  Timing (in seconds)
% 3.08/1.60  ----------------------
% 3.08/1.61  Preprocessing        : 0.41
% 3.08/1.61  Parsing              : 0.23
% 3.08/1.61  CNF conversion       : 0.03
% 3.08/1.61  Main loop            : 0.41
% 3.08/1.61  Inferencing          : 0.14
% 3.08/1.61  Reduction            : 0.14
% 3.08/1.61  Demodulation         : 0.11
% 3.08/1.61  BG Simplification    : 0.02
% 3.08/1.61  Subsumption          : 0.07
% 3.08/1.61  Abstraction          : 0.02
% 3.08/1.61  MUC search           : 0.00
% 3.08/1.61  Cooper               : 0.00
% 3.08/1.61  Total                : 0.86
% 3.08/1.61  Index Insertion      : 0.00
% 3.08/1.61  Index Deletion       : 0.00
% 3.08/1.61  Index Matching       : 0.00
% 3.08/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
