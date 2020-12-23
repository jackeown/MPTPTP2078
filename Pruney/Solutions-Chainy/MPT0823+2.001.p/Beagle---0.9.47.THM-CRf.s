%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:12 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 415 expanded)
%              Number of leaves         :   30 ( 153 expanded)
%              Depth                    :   23
%              Number of atoms          :  236 ( 967 expanded)
%              Number of equality atoms :   62 ( 256 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
          & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_366,plain,(
    ! [C_151,A_152,B_153] :
      ( v4_relat_1(C_151,A_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_370,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_366])).

tff(c_361,plain,(
    ! [C_148,B_149,A_150] :
      ( v5_relat_1(C_148,B_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_365,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_361])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_relat_1(k4_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [B_33,A_34] :
      ( v5_relat_1(B_33,A_34)
      | ~ r1_tarski(k2_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_6,A_34] :
      ( v5_relat_1(k4_relat_1(A_6),A_34)
      | ~ r1_tarski(k1_relat_1(A_6),A_34)
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_61])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [C_163,A_164,B_165] :
      ( m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ r1_tarski(k2_relat_1(C_163),B_165)
      | ~ r1_tarski(k1_relat_1(C_163),A_164)
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_478,plain,(
    ! [A_184,B_185,C_186] :
      ( k1_relset_1(A_184,B_185,C_186) = k1_relat_1(C_186)
      | ~ r1_tarski(k2_relat_1(C_186),B_185)
      | ~ r1_tarski(k1_relat_1(C_186),A_184)
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_410,c_22])).

tff(c_484,plain,(
    ! [A_187,A_188,B_189] :
      ( k1_relset_1(A_187,A_188,B_189) = k1_relat_1(B_189)
      | ~ r1_tarski(k1_relat_1(B_189),A_187)
      | ~ v5_relat_1(B_189,A_188)
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_8,c_478])).

tff(c_532,plain,(
    ! [A_204,A_205,A_206] :
      ( k1_relset_1(A_204,A_205,k4_relat_1(A_206)) = k1_relat_1(k4_relat_1(A_206))
      | ~ r1_tarski(k2_relat_1(A_206),A_204)
      | ~ v5_relat_1(k4_relat_1(A_206),A_205)
      | ~ v1_relat_1(k4_relat_1(A_206))
      | ~ v1_relat_1(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_484])).

tff(c_538,plain,(
    ! [A_207,A_208,B_209] :
      ( k1_relset_1(A_207,A_208,k4_relat_1(B_209)) = k1_relat_1(k4_relat_1(B_209))
      | ~ v5_relat_1(k4_relat_1(B_209),A_208)
      | ~ v1_relat_1(k4_relat_1(B_209))
      | ~ v5_relat_1(B_209,A_207)
      | ~ v1_relat_1(B_209) ) ),
    inference(resolution,[status(thm)],[c_8,c_532])).

tff(c_548,plain,(
    ! [A_213,A_214,A_215] :
      ( k1_relset_1(A_213,A_214,k4_relat_1(A_215)) = k1_relat_1(k4_relat_1(A_215))
      | ~ v5_relat_1(A_215,A_213)
      | ~ r1_tarski(k1_relat_1(A_215),A_214)
      | ~ v1_relat_1(k4_relat_1(A_215))
      | ~ v1_relat_1(A_215) ) ),
    inference(resolution,[status(thm)],[c_67,c_538])).

tff(c_554,plain,(
    ! [A_216,A_217,B_218] :
      ( k1_relset_1(A_216,A_217,k4_relat_1(B_218)) = k1_relat_1(k4_relat_1(B_218))
      | ~ v5_relat_1(B_218,A_216)
      | ~ v1_relat_1(k4_relat_1(B_218))
      | ~ v4_relat_1(B_218,A_217)
      | ~ v1_relat_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_4,c_548])).

tff(c_558,plain,(
    ! [A_219,A_220,A_221] :
      ( k1_relset_1(A_219,A_220,k4_relat_1(A_221)) = k1_relat_1(k4_relat_1(A_221))
      | ~ v5_relat_1(A_221,A_219)
      | ~ v4_relat_1(A_221,A_220)
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_10,c_554])).

tff(c_400,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_relset_1(A_160,B_161,C_162) = k2_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_404,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_400])).

tff(c_385,plain,(
    ! [A_157,B_158,C_159] :
      ( k3_relset_1(A_157,B_158,C_159) = k4_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_389,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_385])).

tff(c_87,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_82,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_69,plain,(
    ! [B_35,A_36] :
      ( v4_relat_1(B_35,A_36)
      | ~ r1_tarski(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_6,A_36] :
      ( v4_relat_1(k4_relat_1(A_6),A_36)
      | ~ r1_tarski(k2_relat_1(A_6),A_36)
      | ~ v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_122,plain,(
    ! [C_56,A_57,B_58] :
      ( m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ r1_tarski(k2_relat_1(C_56),B_58)
      | ~ r1_tarski(k1_relat_1(C_56),A_57)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_197,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ r1_tarski(k2_relat_1(C_83),B_82)
      | ~ r1_tarski(k1_relat_1(C_83),A_81)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_122,c_22])).

tff(c_259,plain,(
    ! [A_107,B_108,A_109] :
      ( k1_relset_1(A_107,B_108,k4_relat_1(A_109)) = k1_relat_1(k4_relat_1(A_109))
      | ~ r1_tarski(k1_relat_1(A_109),B_108)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(A_109)),A_107)
      | ~ v1_relat_1(k4_relat_1(A_109))
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_197])).

tff(c_284,plain,(
    ! [A_119,A_120,B_121] :
      ( k1_relset_1(A_119,A_120,k4_relat_1(B_121)) = k1_relat_1(k4_relat_1(B_121))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(B_121)),A_119)
      | ~ v1_relat_1(k4_relat_1(B_121))
      | ~ v4_relat_1(B_121,A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_4,c_259])).

tff(c_291,plain,(
    ! [A_122,A_123,B_124] :
      ( k1_relset_1(A_122,A_123,k4_relat_1(B_124)) = k1_relat_1(k4_relat_1(B_124))
      | ~ v4_relat_1(B_124,A_123)
      | ~ v1_relat_1(B_124)
      | ~ v4_relat_1(k4_relat_1(B_124),A_122)
      | ~ v1_relat_1(k4_relat_1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_4,c_284])).

tff(c_314,plain,(
    ! [A_134,A_135,A_136] :
      ( k1_relset_1(A_134,A_135,k4_relat_1(A_136)) = k1_relat_1(k4_relat_1(A_136))
      | ~ v4_relat_1(A_136,A_135)
      | ~ r1_tarski(k2_relat_1(A_136),A_134)
      | ~ v1_relat_1(k4_relat_1(A_136))
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_72,c_291])).

tff(c_326,plain,(
    ! [A_140,A_141,B_142] :
      ( k1_relset_1(A_140,A_141,k4_relat_1(B_142)) = k1_relat_1(k4_relat_1(B_142))
      | ~ v4_relat_1(B_142,A_141)
      | ~ v1_relat_1(k4_relat_1(B_142))
      | ~ v5_relat_1(B_142,A_140)
      | ~ v1_relat_1(B_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_314])).

tff(c_330,plain,(
    ! [A_143,A_144,A_145] :
      ( k1_relset_1(A_143,A_144,k4_relat_1(A_145)) = k1_relat_1(k4_relat_1(A_145))
      | ~ v4_relat_1(A_145,A_144)
      | ~ v5_relat_1(A_145,A_143)
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_10,c_326])).

tff(c_111,plain,(
    ! [A_51,B_52,C_53] :
      ( k3_relset_1(A_51,B_52,C_53) = k4_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_111])).

tff(c_92,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_30,plain,
    ( k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_97,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_73])).

tff(c_116,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_97])).

tff(c_336,plain,
    ( k1_relat_1(k4_relat_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_116])).

tff(c_342,plain,(
    k1_relat_1(k4_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_91,c_86,c_336])).

tff(c_346,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_342])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_346])).

tff(c_352,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_391,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_352])).

tff(c_405,plain,(
    k1_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_391])).

tff(c_564,plain,
    ( k1_relat_1(k4_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_405])).

tff(c_573,plain,(
    k1_relat_1(k4_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_370,c_365,c_564])).

tff(c_590,plain,(
    ! [A_1] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_1)
      | ~ v4_relat_1(k4_relat_1('#skF_3'),A_1)
      | ~ v1_relat_1(k4_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_4])).

tff(c_611,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_614,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_611])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_614])).

tff(c_620,plain,(
    v1_relat_1(k4_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_505,plain,(
    ! [A_194,B_195,C_196] :
      ( k2_relset_1(A_194,B_195,C_196) = k2_relat_1(C_196)
      | ~ r1_tarski(k2_relat_1(C_196),B_195)
      | ~ r1_tarski(k1_relat_1(C_196),A_194)
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_410,c_24])).

tff(c_510,plain,(
    ! [A_194,A_3,B_4] :
      ( k2_relset_1(A_194,A_3,B_4) = k2_relat_1(B_4)
      | ~ r1_tarski(k1_relat_1(B_4),A_194)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_505])).

tff(c_583,plain,(
    ! [A_194,A_3] :
      ( k2_relset_1(A_194,A_3,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_194)
      | ~ v5_relat_1(k4_relat_1('#skF_3'),A_3)
      | ~ v1_relat_1(k4_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_510])).

tff(c_670,plain,(
    ! [A_231,A_232] :
      ( k2_relset_1(A_231,A_232,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_231)
      | ~ v5_relat_1(k4_relat_1('#skF_3'),A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_583])).

tff(c_673,plain,(
    ! [A_3,A_232] :
      ( k2_relset_1(A_3,A_232,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1(k4_relat_1('#skF_3'),A_232)
      | ~ v5_relat_1('#skF_3',A_3)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_670])).

tff(c_716,plain,(
    ! [A_237,A_238] :
      ( k2_relset_1(A_237,A_238,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1(k4_relat_1('#skF_3'),A_238)
      | ~ v5_relat_1('#skF_3',A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_673])).

tff(c_719,plain,(
    ! [A_237,A_34] :
      ( k2_relset_1(A_237,A_34,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1('#skF_3',A_237)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_34)
      | ~ v1_relat_1(k4_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_716])).

tff(c_723,plain,(
    ! [A_239,A_240] :
      ( k2_relset_1(A_239,A_240,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1('#skF_3',A_239)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_620,c_719])).

tff(c_726,plain,(
    ! [A_239,A_1] :
      ( k2_relset_1(A_239,A_1,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1('#skF_3',A_239)
      | ~ v4_relat_1('#skF_3',A_1)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_723])).

tff(c_730,plain,(
    ! [A_241,A_242] :
      ( k2_relset_1(A_241,A_242,k4_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_3'))
      | ~ v5_relat_1('#skF_3',A_241)
      | ~ v4_relat_1('#skF_3',A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_726])).

tff(c_375,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_relset_1(A_154,B_155,C_156) = k1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_379,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_375])).

tff(c_351,plain,(
    k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_380,plain,(
    k2_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_351])).

tff(c_390,plain,(
    k2_relset_1('#skF_2','#skF_1',k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_380])).

tff(c_736,plain,
    ( k2_relat_1(k4_relat_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_390])).

tff(c_742,plain,(
    k2_relat_1(k4_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_365,c_736])).

tff(c_756,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_742])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.07/1.52  
% 3.07/1.52  %Foreground sorts:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Background operators:
% 3.07/1.52  
% 3.07/1.52  
% 3.07/1.52  %Foreground operators:
% 3.07/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.52  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.07/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.07/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.07/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.07/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.52  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.07/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.52  
% 3.25/1.55  tff(f_84, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 3.25/1.55  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.25/1.55  tff(f_47, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.25/1.55  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.25/1.55  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.25/1.55  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.25/1.55  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.25/1.55  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.25/1.55  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/1.55  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.55  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.25/1.55  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.55  tff(c_52, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.55  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_52])).
% 3.25/1.55  tff(c_12, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.25/1.55  tff(c_366, plain, (![C_151, A_152, B_153]: (v4_relat_1(C_151, A_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.55  tff(c_370, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_366])).
% 3.25/1.55  tff(c_361, plain, (![C_148, B_149, A_150]: (v5_relat_1(C_148, B_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.55  tff(c_365, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_361])).
% 3.25/1.55  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.55  tff(c_10, plain, (![A_5]: (v1_relat_1(k4_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.55  tff(c_61, plain, (![B_33, A_34]: (v5_relat_1(B_33, A_34) | ~r1_tarski(k2_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.55  tff(c_67, plain, (![A_6, A_34]: (v5_relat_1(k4_relat_1(A_6), A_34) | ~r1_tarski(k1_relat_1(A_6), A_34) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_61])).
% 3.25/1.55  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.55  tff(c_14, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.25/1.55  tff(c_410, plain, (![C_163, A_164, B_165]: (m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~r1_tarski(k2_relat_1(C_163), B_165) | ~r1_tarski(k1_relat_1(C_163), A_164) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.25/1.55  tff(c_22, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.55  tff(c_478, plain, (![A_184, B_185, C_186]: (k1_relset_1(A_184, B_185, C_186)=k1_relat_1(C_186) | ~r1_tarski(k2_relat_1(C_186), B_185) | ~r1_tarski(k1_relat_1(C_186), A_184) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_410, c_22])).
% 3.25/1.55  tff(c_484, plain, (![A_187, A_188, B_189]: (k1_relset_1(A_187, A_188, B_189)=k1_relat_1(B_189) | ~r1_tarski(k1_relat_1(B_189), A_187) | ~v5_relat_1(B_189, A_188) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_8, c_478])).
% 3.25/1.55  tff(c_532, plain, (![A_204, A_205, A_206]: (k1_relset_1(A_204, A_205, k4_relat_1(A_206))=k1_relat_1(k4_relat_1(A_206)) | ~r1_tarski(k2_relat_1(A_206), A_204) | ~v5_relat_1(k4_relat_1(A_206), A_205) | ~v1_relat_1(k4_relat_1(A_206)) | ~v1_relat_1(A_206))), inference(superposition, [status(thm), theory('equality')], [c_14, c_484])).
% 3.25/1.55  tff(c_538, plain, (![A_207, A_208, B_209]: (k1_relset_1(A_207, A_208, k4_relat_1(B_209))=k1_relat_1(k4_relat_1(B_209)) | ~v5_relat_1(k4_relat_1(B_209), A_208) | ~v1_relat_1(k4_relat_1(B_209)) | ~v5_relat_1(B_209, A_207) | ~v1_relat_1(B_209))), inference(resolution, [status(thm)], [c_8, c_532])).
% 3.25/1.55  tff(c_548, plain, (![A_213, A_214, A_215]: (k1_relset_1(A_213, A_214, k4_relat_1(A_215))=k1_relat_1(k4_relat_1(A_215)) | ~v5_relat_1(A_215, A_213) | ~r1_tarski(k1_relat_1(A_215), A_214) | ~v1_relat_1(k4_relat_1(A_215)) | ~v1_relat_1(A_215))), inference(resolution, [status(thm)], [c_67, c_538])).
% 3.25/1.55  tff(c_554, plain, (![A_216, A_217, B_218]: (k1_relset_1(A_216, A_217, k4_relat_1(B_218))=k1_relat_1(k4_relat_1(B_218)) | ~v5_relat_1(B_218, A_216) | ~v1_relat_1(k4_relat_1(B_218)) | ~v4_relat_1(B_218, A_217) | ~v1_relat_1(B_218))), inference(resolution, [status(thm)], [c_4, c_548])).
% 3.25/1.55  tff(c_558, plain, (![A_219, A_220, A_221]: (k1_relset_1(A_219, A_220, k4_relat_1(A_221))=k1_relat_1(k4_relat_1(A_221)) | ~v5_relat_1(A_221, A_219) | ~v4_relat_1(A_221, A_220) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_10, c_554])).
% 3.25/1.55  tff(c_400, plain, (![A_160, B_161, C_162]: (k2_relset_1(A_160, B_161, C_162)=k2_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.55  tff(c_404, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_400])).
% 3.25/1.55  tff(c_385, plain, (![A_157, B_158, C_159]: (k3_relset_1(A_157, B_158, C_159)=k4_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.55  tff(c_389, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_385])).
% 3.25/1.55  tff(c_87, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.55  tff(c_91, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_87])).
% 3.25/1.55  tff(c_82, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.55  tff(c_86, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_82])).
% 3.25/1.55  tff(c_69, plain, (![B_35, A_36]: (v4_relat_1(B_35, A_36) | ~r1_tarski(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.55  tff(c_72, plain, (![A_6, A_36]: (v4_relat_1(k4_relat_1(A_6), A_36) | ~r1_tarski(k2_relat_1(A_6), A_36) | ~v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_69])).
% 3.25/1.55  tff(c_122, plain, (![C_56, A_57, B_58]: (m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~r1_tarski(k2_relat_1(C_56), B_58) | ~r1_tarski(k1_relat_1(C_56), A_57) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.25/1.55  tff(c_197, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~r1_tarski(k2_relat_1(C_83), B_82) | ~r1_tarski(k1_relat_1(C_83), A_81) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_122, c_22])).
% 3.25/1.55  tff(c_259, plain, (![A_107, B_108, A_109]: (k1_relset_1(A_107, B_108, k4_relat_1(A_109))=k1_relat_1(k4_relat_1(A_109)) | ~r1_tarski(k1_relat_1(A_109), B_108) | ~r1_tarski(k1_relat_1(k4_relat_1(A_109)), A_107) | ~v1_relat_1(k4_relat_1(A_109)) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_12, c_197])).
% 3.25/1.55  tff(c_284, plain, (![A_119, A_120, B_121]: (k1_relset_1(A_119, A_120, k4_relat_1(B_121))=k1_relat_1(k4_relat_1(B_121)) | ~r1_tarski(k1_relat_1(k4_relat_1(B_121)), A_119) | ~v1_relat_1(k4_relat_1(B_121)) | ~v4_relat_1(B_121, A_120) | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_4, c_259])).
% 3.25/1.55  tff(c_291, plain, (![A_122, A_123, B_124]: (k1_relset_1(A_122, A_123, k4_relat_1(B_124))=k1_relat_1(k4_relat_1(B_124)) | ~v4_relat_1(B_124, A_123) | ~v1_relat_1(B_124) | ~v4_relat_1(k4_relat_1(B_124), A_122) | ~v1_relat_1(k4_relat_1(B_124)))), inference(resolution, [status(thm)], [c_4, c_284])).
% 3.25/1.55  tff(c_314, plain, (![A_134, A_135, A_136]: (k1_relset_1(A_134, A_135, k4_relat_1(A_136))=k1_relat_1(k4_relat_1(A_136)) | ~v4_relat_1(A_136, A_135) | ~r1_tarski(k2_relat_1(A_136), A_134) | ~v1_relat_1(k4_relat_1(A_136)) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_72, c_291])).
% 3.25/1.55  tff(c_326, plain, (![A_140, A_141, B_142]: (k1_relset_1(A_140, A_141, k4_relat_1(B_142))=k1_relat_1(k4_relat_1(B_142)) | ~v4_relat_1(B_142, A_141) | ~v1_relat_1(k4_relat_1(B_142)) | ~v5_relat_1(B_142, A_140) | ~v1_relat_1(B_142))), inference(resolution, [status(thm)], [c_8, c_314])).
% 3.25/1.55  tff(c_330, plain, (![A_143, A_144, A_145]: (k1_relset_1(A_143, A_144, k4_relat_1(A_145))=k1_relat_1(k4_relat_1(A_145)) | ~v4_relat_1(A_145, A_144) | ~v5_relat_1(A_145, A_143) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_10, c_326])).
% 3.25/1.55  tff(c_111, plain, (![A_51, B_52, C_53]: (k3_relset_1(A_51, B_52, C_53)=k4_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.55  tff(c_115, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_111])).
% 3.25/1.55  tff(c_92, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.55  tff(c_96, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_92])).
% 3.25/1.55  tff(c_30, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.55  tff(c_73, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 3.25/1.55  tff(c_97, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_73])).
% 3.25/1.55  tff(c_116, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_97])).
% 3.25/1.55  tff(c_336, plain, (k1_relat_1(k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v4_relat_1('#skF_3', '#skF_1') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_330, c_116])).
% 3.25/1.55  tff(c_342, plain, (k1_relat_1(k4_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_91, c_86, c_336])).
% 3.25/1.55  tff(c_346, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_342])).
% 3.25/1.55  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_346])).
% 3.25/1.55  tff(c_352, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.25/1.55  tff(c_391, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_352])).
% 3.25/1.55  tff(c_405, plain, (k1_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_391])).
% 3.25/1.55  tff(c_564, plain, (k1_relat_1(k4_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_558, c_405])).
% 3.25/1.55  tff(c_573, plain, (k1_relat_1(k4_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_370, c_365, c_564])).
% 3.25/1.55  tff(c_590, plain, (![A_1]: (r1_tarski(k2_relat_1('#skF_3'), A_1) | ~v4_relat_1(k4_relat_1('#skF_3'), A_1) | ~v1_relat_1(k4_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_573, c_4])).
% 3.25/1.55  tff(c_611, plain, (~v1_relat_1(k4_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_590])).
% 3.25/1.55  tff(c_614, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_611])).
% 3.25/1.55  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_614])).
% 3.25/1.55  tff(c_620, plain, (v1_relat_1(k4_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_590])).
% 3.25/1.55  tff(c_24, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.55  tff(c_505, plain, (![A_194, B_195, C_196]: (k2_relset_1(A_194, B_195, C_196)=k2_relat_1(C_196) | ~r1_tarski(k2_relat_1(C_196), B_195) | ~r1_tarski(k1_relat_1(C_196), A_194) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_410, c_24])).
% 3.25/1.55  tff(c_510, plain, (![A_194, A_3, B_4]: (k2_relset_1(A_194, A_3, B_4)=k2_relat_1(B_4) | ~r1_tarski(k1_relat_1(B_4), A_194) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_505])).
% 3.25/1.55  tff(c_583, plain, (![A_194, A_3]: (k2_relset_1(A_194, A_3, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), A_194) | ~v5_relat_1(k4_relat_1('#skF_3'), A_3) | ~v1_relat_1(k4_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_573, c_510])).
% 3.25/1.55  tff(c_670, plain, (![A_231, A_232]: (k2_relset_1(A_231, A_232, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), A_231) | ~v5_relat_1(k4_relat_1('#skF_3'), A_232))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_583])).
% 3.25/1.55  tff(c_673, plain, (![A_3, A_232]: (k2_relset_1(A_3, A_232, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1(k4_relat_1('#skF_3'), A_232) | ~v5_relat_1('#skF_3', A_3) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_670])).
% 3.25/1.55  tff(c_716, plain, (![A_237, A_238]: (k2_relset_1(A_237, A_238, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1(k4_relat_1('#skF_3'), A_238) | ~v5_relat_1('#skF_3', A_237))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_673])).
% 3.25/1.55  tff(c_719, plain, (![A_237, A_34]: (k2_relset_1(A_237, A_34, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', A_237) | ~r1_tarski(k1_relat_1('#skF_3'), A_34) | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_67, c_716])).
% 3.25/1.55  tff(c_723, plain, (![A_239, A_240]: (k2_relset_1(A_239, A_240, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', A_239) | ~r1_tarski(k1_relat_1('#skF_3'), A_240))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_620, c_719])).
% 3.25/1.55  tff(c_726, plain, (![A_239, A_1]: (k2_relset_1(A_239, A_1, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', A_239) | ~v4_relat_1('#skF_3', A_1) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_723])).
% 3.25/1.55  tff(c_730, plain, (![A_241, A_242]: (k2_relset_1(A_241, A_242, k4_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', A_241) | ~v4_relat_1('#skF_3', A_242))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_726])).
% 3.25/1.55  tff(c_375, plain, (![A_154, B_155, C_156]: (k1_relset_1(A_154, B_155, C_156)=k1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.55  tff(c_379, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_375])).
% 3.25/1.55  tff(c_351, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.25/1.55  tff(c_380, plain, (k2_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_351])).
% 3.25/1.55  tff(c_390, plain, (k2_relset_1('#skF_2', '#skF_1', k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_380])).
% 3.25/1.55  tff(c_736, plain, (k2_relat_1(k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v4_relat_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_730, c_390])).
% 3.25/1.55  tff(c_742, plain, (k2_relat_1(k4_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_365, c_736])).
% 3.25/1.55  tff(c_756, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_742])).
% 3.25/1.55  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_756])).
% 3.25/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.55  
% 3.25/1.55  Inference rules
% 3.25/1.55  ----------------------
% 3.25/1.55  #Ref     : 0
% 3.25/1.55  #Sup     : 178
% 3.25/1.55  #Fact    : 0
% 3.25/1.55  #Define  : 0
% 3.25/1.55  #Split   : 2
% 3.25/1.55  #Chain   : 0
% 3.25/1.55  #Close   : 0
% 3.25/1.55  
% 3.25/1.55  Ordering : KBO
% 3.25/1.55  
% 3.25/1.55  Simplification rules
% 3.25/1.55  ----------------------
% 3.25/1.55  #Subsume      : 8
% 3.25/1.55  #Demod        : 61
% 3.25/1.55  #Tautology    : 61
% 3.25/1.55  #SimpNegUnit  : 0
% 3.25/1.55  #BackRed      : 6
% 3.25/1.55  
% 3.25/1.55  #Partial instantiations: 0
% 3.25/1.55  #Strategies tried      : 1
% 3.25/1.55  
% 3.25/1.55  Timing (in seconds)
% 3.25/1.55  ----------------------
% 3.25/1.55  Preprocessing        : 0.33
% 3.25/1.55  Parsing              : 0.18
% 3.25/1.55  CNF conversion       : 0.02
% 3.25/1.55  Main loop            : 0.39
% 3.25/1.55  Inferencing          : 0.16
% 3.25/1.55  Reduction            : 0.10
% 3.25/1.55  Demodulation         : 0.07
% 3.25/1.55  BG Simplification    : 0.02
% 3.25/1.55  Subsumption          : 0.07
% 3.25/1.55  Abstraction          : 0.02
% 3.25/1.55  MUC search           : 0.00
% 3.25/1.55  Cooper               : 0.00
% 3.25/1.55  Total                : 0.77
% 3.25/1.55  Index Insertion      : 0.00
% 3.25/1.55  Index Deletion       : 0.00
% 3.25/1.55  Index Matching       : 0.00
% 3.25/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
