%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:12 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 165 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 349 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
          & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_55,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_308,plain,(
    ! [C_121,B_122,A_123] :
      ( v5_relat_1(C_121,B_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_312,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_308])).

tff(c_303,plain,(
    ! [C_118,A_119,B_120] :
      ( v4_relat_1(C_118,A_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_307,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_303])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_relat_1(k4_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    ! [B_34,A_35] :
      ( v4_relat_1(B_34,A_35)
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [A_11,A_35] :
      ( v4_relat_1(k4_relat_1(A_11),A_35)
      | ~ r1_tarski(k2_relat_1(A_11),A_35)
      | ~ v1_relat_1(k4_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_62])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_355,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_457,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ r1_tarski(k2_relat_1(C_168),B_167)
      | ~ r1_tarski(k1_relat_1(C_168),A_166)
      | ~ v1_relat_1(C_168) ) ),
    inference(resolution,[status(thm)],[c_355,c_26])).

tff(c_490,plain,(
    ! [A_179,B_180,A_181] :
      ( k2_relset_1(A_179,B_180,k4_relat_1(A_181)) = k2_relat_1(k4_relat_1(A_181))
      | ~ r1_tarski(k1_relat_1(A_181),B_180)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(A_181)),A_179)
      | ~ v1_relat_1(k4_relat_1(A_181))
      | ~ v1_relat_1(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_457])).

tff(c_519,plain,(
    ! [A_194,A_195,B_196] :
      ( k2_relset_1(A_194,A_195,k4_relat_1(B_196)) = k2_relat_1(k4_relat_1(B_196))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(B_196)),A_194)
      | ~ v1_relat_1(k4_relat_1(B_196))
      | ~ v4_relat_1(B_196,A_195)
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_6,c_490])).

tff(c_526,plain,(
    ! [A_197,A_198,B_199] :
      ( k2_relset_1(A_197,A_198,k4_relat_1(B_199)) = k2_relat_1(k4_relat_1(B_199))
      | ~ v4_relat_1(B_199,A_198)
      | ~ v1_relat_1(B_199)
      | ~ v4_relat_1(k4_relat_1(B_199),A_197)
      | ~ v1_relat_1(k4_relat_1(B_199)) ) ),
    inference(resolution,[status(thm)],[c_6,c_519])).

tff(c_530,plain,(
    ! [A_200,A_201,A_202] :
      ( k2_relset_1(A_200,A_201,k4_relat_1(A_202)) = k2_relat_1(k4_relat_1(A_202))
      | ~ v4_relat_1(A_202,A_201)
      | ~ r1_tarski(k2_relat_1(A_202),A_200)
      | ~ v1_relat_1(k4_relat_1(A_202))
      | ~ v1_relat_1(A_202) ) ),
    inference(resolution,[status(thm)],[c_65,c_526])).

tff(c_536,plain,(
    ! [A_203,A_204,B_205] :
      ( k2_relset_1(A_203,A_204,k4_relat_1(B_205)) = k2_relat_1(k4_relat_1(B_205))
      | ~ v4_relat_1(B_205,A_204)
      | ~ v1_relat_1(k4_relat_1(B_205))
      | ~ v5_relat_1(B_205,A_203)
      | ~ v1_relat_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_10,c_530])).

tff(c_540,plain,(
    ! [A_206,A_207,A_208] :
      ( k2_relset_1(A_206,A_207,k4_relat_1(A_208)) = k2_relat_1(k4_relat_1(A_208))
      | ~ v4_relat_1(A_208,A_207)
      | ~ v5_relat_1(A_208,A_206)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_12,c_536])).

tff(c_335,plain,(
    ! [A_129,B_130,C_131] :
      ( k3_relset_1(A_129,B_130,C_131) = k4_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_339,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_335])).

tff(c_325,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_329,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_325])).

tff(c_79,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_83,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_92,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(C_45,B_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_84,plain,(
    ! [B_43,A_44] :
      ( v5_relat_1(B_43,A_44)
      | ~ r1_tarski(k2_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [A_11,A_44] :
      ( v5_relat_1(k4_relat_1(A_11),A_44)
      | ~ r1_tarski(k1_relat_1(A_11),A_44)
      | ~ v1_relat_1(k4_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_84])).

tff(c_126,plain,(
    ! [C_57,A_58,B_59] :
      ( m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ r1_tarski(k2_relat_1(C_57),B_59)
      | ~ r1_tarski(k1_relat_1(C_57),A_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_165,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ r1_tarski(k2_relat_1(C_70),B_69)
      | ~ r1_tarski(k1_relat_1(C_70),A_68)
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_171,plain,(
    ! [A_71,A_72,B_73] :
      ( k1_relset_1(A_71,A_72,B_73) = k1_relat_1(B_73)
      | ~ r1_tarski(k1_relat_1(B_73),A_71)
      | ~ v5_relat_1(B_73,A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_246,plain,(
    ! [A_98,A_99,A_100] :
      ( k1_relset_1(A_98,A_99,k4_relat_1(A_100)) = k1_relat_1(k4_relat_1(A_100))
      | ~ r1_tarski(k2_relat_1(A_100),A_98)
      | ~ v5_relat_1(k4_relat_1(A_100),A_99)
      | ~ v1_relat_1(k4_relat_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_171])).

tff(c_252,plain,(
    ! [A_101,A_102,B_103] :
      ( k1_relset_1(A_101,A_102,k4_relat_1(B_103)) = k1_relat_1(k4_relat_1(B_103))
      | ~ v5_relat_1(k4_relat_1(B_103),A_102)
      | ~ v1_relat_1(k4_relat_1(B_103))
      | ~ v5_relat_1(B_103,A_101)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_10,c_246])).

tff(c_256,plain,(
    ! [A_104,A_105,A_106] :
      ( k1_relset_1(A_104,A_105,k4_relat_1(A_106)) = k1_relat_1(k4_relat_1(A_106))
      | ~ v5_relat_1(A_106,A_104)
      | ~ r1_tarski(k1_relat_1(A_106),A_105)
      | ~ v1_relat_1(k4_relat_1(A_106))
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_90,c_252])).

tff(c_268,plain,(
    ! [A_110,A_111,B_112] :
      ( k1_relset_1(A_110,A_111,k4_relat_1(B_112)) = k1_relat_1(k4_relat_1(B_112))
      | ~ v5_relat_1(B_112,A_110)
      | ~ v1_relat_1(k4_relat_1(B_112))
      | ~ v4_relat_1(B_112,A_111)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_272,plain,(
    ! [A_113,A_114,A_115] :
      ( k1_relset_1(A_113,A_114,k4_relat_1(A_115)) = k1_relat_1(k4_relat_1(A_115))
      | ~ v5_relat_1(A_115,A_113)
      | ~ v4_relat_1(A_115,A_114)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_116,plain,(
    ! [A_54,B_55,C_56] :
      ( k3_relset_1(A_54,B_55,C_56) = k4_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_97,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_32,plain,
    ( k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_70,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_102,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70])).

tff(c_121,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_102])).

tff(c_278,plain,
    ( k1_relat_1(k4_relat_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_121])).

tff(c_284,plain,(
    k1_relat_1(k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_83,c_96,c_278])).

tff(c_288,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_288])).

tff(c_293,plain,(
    k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_330,plain,(
    k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_293])).

tff(c_340,plain,(
    k2_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_330])).

tff(c_546,plain,
    ( k2_relat_1(k4_relat_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_340])).

tff(c_552,plain,(
    k2_relat_1(k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_312,c_307,c_546])).

tff(c_562,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_552])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  
% 2.90/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.47  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.47  
% 2.90/1.47  %Foreground sorts:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Background operators:
% 2.90/1.47  
% 2.90/1.47  
% 2.90/1.47  %Foreground operators:
% 2.90/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.47  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 2.90/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.90/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.48  
% 2.90/1.49  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.90/1.49  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 2.90/1.49  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.49  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.90/1.49  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.49  tff(f_48, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.90/1.49  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.90/1.49  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.49  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.90/1.49  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.90/1.49  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 2.90/1.49  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.49  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.90/1.49  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.90/1.49  tff(c_55, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.49  tff(c_58, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.90/1.49  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 2.90/1.49  tff(c_16, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.90/1.49  tff(c_308, plain, (![C_121, B_122, A_123]: (v5_relat_1(C_121, B_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_122))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.49  tff(c_312, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_308])).
% 2.90/1.49  tff(c_303, plain, (![C_118, A_119, B_120]: (v4_relat_1(C_118, A_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.49  tff(c_307, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_303])).
% 2.90/1.49  tff(c_12, plain, (![A_8]: (v1_relat_1(k4_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.49  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.90/1.49  tff(c_18, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.90/1.49  tff(c_62, plain, (![B_34, A_35]: (v4_relat_1(B_34, A_35) | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.49  tff(c_65, plain, (![A_11, A_35]: (v4_relat_1(k4_relat_1(A_11), A_35) | ~r1_tarski(k2_relat_1(A_11), A_35) | ~v1_relat_1(k4_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_62])).
% 2.90/1.49  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.49  tff(c_355, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.49  tff(c_26, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.49  tff(c_457, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~r1_tarski(k2_relat_1(C_168), B_167) | ~r1_tarski(k1_relat_1(C_168), A_166) | ~v1_relat_1(C_168))), inference(resolution, [status(thm)], [c_355, c_26])).
% 2.90/1.49  tff(c_490, plain, (![A_179, B_180, A_181]: (k2_relset_1(A_179, B_180, k4_relat_1(A_181))=k2_relat_1(k4_relat_1(A_181)) | ~r1_tarski(k1_relat_1(A_181), B_180) | ~r1_tarski(k1_relat_1(k4_relat_1(A_181)), A_179) | ~v1_relat_1(k4_relat_1(A_181)) | ~v1_relat_1(A_181))), inference(superposition, [status(thm), theory('equality')], [c_16, c_457])).
% 2.90/1.49  tff(c_519, plain, (![A_194, A_195, B_196]: (k2_relset_1(A_194, A_195, k4_relat_1(B_196))=k2_relat_1(k4_relat_1(B_196)) | ~r1_tarski(k1_relat_1(k4_relat_1(B_196)), A_194) | ~v1_relat_1(k4_relat_1(B_196)) | ~v4_relat_1(B_196, A_195) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_6, c_490])).
% 2.90/1.49  tff(c_526, plain, (![A_197, A_198, B_199]: (k2_relset_1(A_197, A_198, k4_relat_1(B_199))=k2_relat_1(k4_relat_1(B_199)) | ~v4_relat_1(B_199, A_198) | ~v1_relat_1(B_199) | ~v4_relat_1(k4_relat_1(B_199), A_197) | ~v1_relat_1(k4_relat_1(B_199)))), inference(resolution, [status(thm)], [c_6, c_519])).
% 2.90/1.49  tff(c_530, plain, (![A_200, A_201, A_202]: (k2_relset_1(A_200, A_201, k4_relat_1(A_202))=k2_relat_1(k4_relat_1(A_202)) | ~v4_relat_1(A_202, A_201) | ~r1_tarski(k2_relat_1(A_202), A_200) | ~v1_relat_1(k4_relat_1(A_202)) | ~v1_relat_1(A_202))), inference(resolution, [status(thm)], [c_65, c_526])).
% 2.90/1.49  tff(c_536, plain, (![A_203, A_204, B_205]: (k2_relset_1(A_203, A_204, k4_relat_1(B_205))=k2_relat_1(k4_relat_1(B_205)) | ~v4_relat_1(B_205, A_204) | ~v1_relat_1(k4_relat_1(B_205)) | ~v5_relat_1(B_205, A_203) | ~v1_relat_1(B_205))), inference(resolution, [status(thm)], [c_10, c_530])).
% 2.90/1.49  tff(c_540, plain, (![A_206, A_207, A_208]: (k2_relset_1(A_206, A_207, k4_relat_1(A_208))=k2_relat_1(k4_relat_1(A_208)) | ~v4_relat_1(A_208, A_207) | ~v5_relat_1(A_208, A_206) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_12, c_536])).
% 2.90/1.49  tff(c_335, plain, (![A_129, B_130, C_131]: (k3_relset_1(A_129, B_130, C_131)=k4_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.90/1.49  tff(c_339, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_335])).
% 2.90/1.49  tff(c_325, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.49  tff(c_329, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_325])).
% 2.90/1.49  tff(c_79, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.49  tff(c_83, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_79])).
% 2.90/1.49  tff(c_92, plain, (![C_45, B_46, A_47]: (v5_relat_1(C_45, B_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.49  tff(c_96, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_92])).
% 2.90/1.49  tff(c_84, plain, (![B_43, A_44]: (v5_relat_1(B_43, A_44) | ~r1_tarski(k2_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.90/1.49  tff(c_90, plain, (![A_11, A_44]: (v5_relat_1(k4_relat_1(A_11), A_44) | ~r1_tarski(k1_relat_1(A_11), A_44) | ~v1_relat_1(k4_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_84])).
% 2.90/1.49  tff(c_126, plain, (![C_57, A_58, B_59]: (m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~r1_tarski(k2_relat_1(C_57), B_59) | ~r1_tarski(k1_relat_1(C_57), A_58) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.49  tff(c_24, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.90/1.49  tff(c_165, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~r1_tarski(k2_relat_1(C_70), B_69) | ~r1_tarski(k1_relat_1(C_70), A_68) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_126, c_24])).
% 2.90/1.49  tff(c_171, plain, (![A_71, A_72, B_73]: (k1_relset_1(A_71, A_72, B_73)=k1_relat_1(B_73) | ~r1_tarski(k1_relat_1(B_73), A_71) | ~v5_relat_1(B_73, A_72) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.90/1.49  tff(c_246, plain, (![A_98, A_99, A_100]: (k1_relset_1(A_98, A_99, k4_relat_1(A_100))=k1_relat_1(k4_relat_1(A_100)) | ~r1_tarski(k2_relat_1(A_100), A_98) | ~v5_relat_1(k4_relat_1(A_100), A_99) | ~v1_relat_1(k4_relat_1(A_100)) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_18, c_171])).
% 2.90/1.49  tff(c_252, plain, (![A_101, A_102, B_103]: (k1_relset_1(A_101, A_102, k4_relat_1(B_103))=k1_relat_1(k4_relat_1(B_103)) | ~v5_relat_1(k4_relat_1(B_103), A_102) | ~v1_relat_1(k4_relat_1(B_103)) | ~v5_relat_1(B_103, A_101) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_10, c_246])).
% 2.90/1.49  tff(c_256, plain, (![A_104, A_105, A_106]: (k1_relset_1(A_104, A_105, k4_relat_1(A_106))=k1_relat_1(k4_relat_1(A_106)) | ~v5_relat_1(A_106, A_104) | ~r1_tarski(k1_relat_1(A_106), A_105) | ~v1_relat_1(k4_relat_1(A_106)) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_90, c_252])).
% 2.90/1.49  tff(c_268, plain, (![A_110, A_111, B_112]: (k1_relset_1(A_110, A_111, k4_relat_1(B_112))=k1_relat_1(k4_relat_1(B_112)) | ~v5_relat_1(B_112, A_110) | ~v1_relat_1(k4_relat_1(B_112)) | ~v4_relat_1(B_112, A_111) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_6, c_256])).
% 2.90/1.49  tff(c_272, plain, (![A_113, A_114, A_115]: (k1_relset_1(A_113, A_114, k4_relat_1(A_115))=k1_relat_1(k4_relat_1(A_115)) | ~v5_relat_1(A_115, A_113) | ~v4_relat_1(A_115, A_114) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_12, c_268])).
% 2.90/1.49  tff(c_116, plain, (![A_54, B_55, C_56]: (k3_relset_1(A_54, B_55, C_56)=k4_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.90/1.49  tff(c_120, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_116])).
% 2.90/1.49  tff(c_97, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.49  tff(c_101, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_97])).
% 2.90/1.49  tff(c_32, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.90/1.49  tff(c_70, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.90/1.49  tff(c_102, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_70])).
% 2.90/1.49  tff(c_121, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_102])).
% 2.90/1.49  tff(c_278, plain, (k1_relat_1(k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_272, c_121])).
% 2.90/1.49  tff(c_284, plain, (k1_relat_1(k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_83, c_96, c_278])).
% 2.90/1.49  tff(c_288, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_284])).
% 2.90/1.49  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_288])).
% 2.90/1.49  tff(c_293, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.90/1.49  tff(c_330, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_293])).
% 2.90/1.49  tff(c_340, plain, (k2_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_330])).
% 2.90/1.49  tff(c_546, plain, (k2_relat_1(k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_540, c_340])).
% 2.90/1.49  tff(c_552, plain, (k2_relat_1(k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_312, c_307, c_546])).
% 2.90/1.49  tff(c_562, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_552])).
% 2.90/1.49  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_562])).
% 2.90/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.49  
% 2.90/1.49  Inference rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Ref     : 0
% 2.90/1.49  #Sup     : 135
% 2.90/1.49  #Fact    : 0
% 2.90/1.49  #Define  : 0
% 2.90/1.49  #Split   : 1
% 2.90/1.49  #Chain   : 0
% 2.90/1.49  #Close   : 0
% 2.90/1.49  
% 2.90/1.49  Ordering : KBO
% 2.90/1.49  
% 2.90/1.49  Simplification rules
% 2.90/1.49  ----------------------
% 2.90/1.49  #Subsume      : 7
% 2.90/1.49  #Demod        : 29
% 2.90/1.49  #Tautology    : 44
% 2.90/1.49  #SimpNegUnit  : 0
% 2.90/1.49  #BackRed      : 6
% 2.90/1.49  
% 2.90/1.49  #Partial instantiations: 0
% 2.90/1.49  #Strategies tried      : 1
% 2.90/1.49  
% 2.90/1.49  Timing (in seconds)
% 2.90/1.49  ----------------------
% 2.90/1.50  Preprocessing        : 0.30
% 2.90/1.50  Parsing              : 0.16
% 2.90/1.50  CNF conversion       : 0.02
% 2.90/1.50  Main loop            : 0.34
% 2.90/1.50  Inferencing          : 0.14
% 2.90/1.50  Reduction            : 0.09
% 2.90/1.50  Demodulation         : 0.06
% 2.90/1.50  BG Simplification    : 0.02
% 2.90/1.50  Subsumption          : 0.06
% 2.90/1.50  Abstraction          : 0.02
% 2.90/1.50  MUC search           : 0.00
% 2.90/1.50  Cooper               : 0.00
% 2.90/1.50  Total                : 0.68
% 2.90/1.50  Index Insertion      : 0.00
% 2.90/1.50  Index Deletion       : 0.00
% 2.90/1.50  Index Matching       : 0.00
% 2.90/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
