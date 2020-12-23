%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 182 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   24
%              Number of atoms          :  233 ( 517 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r8_relat_2 > r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> r8_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

tff(c_44,plain,(
    ! [A_39] : v1_relat_1(k1_wellord2(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_86,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_101,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_4'(A_56,B_57),B_57)
      | r8_relat_2(A_56,B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_56,B_57,B_2] :
      ( r2_hidden('#skF_4'(A_56,B_57),B_2)
      | ~ r1_tarski(B_57,B_2)
      | r8_relat_2(A_56,B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_105,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_6'(A_58,B_59),B_59)
      | r8_relat_2(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_108,plain,(
    ! [A_58,B_59,B_2] :
      ( r2_hidden('#skF_6'(A_58,B_59),B_2)
      | ~ r1_tarski(B_59,B_2)
      | r8_relat_2(A_58,B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_40,plain,(
    ! [A_15,B_29] :
      ( r2_hidden('#skF_5'(A_15,B_29),B_29)
      | r8_relat_2(A_15,B_29)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_154,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(k4_tarski('#skF_5'(A_71,B_72),'#skF_6'(A_71,B_72)),A_71)
      | r8_relat_2(A_71,B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_249,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden(k4_tarski('#skF_5'(A_107,B_108),'#skF_6'(A_107,B_108)),B_109)
      | ~ r1_tarski(A_107,B_109)
      | r8_relat_2(A_107,B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_28,plain,(
    ! [C_13,D_14,A_7] :
      ( r1_tarski(C_13,D_14)
      | ~ r2_hidden(k4_tarski(C_13,D_14),k1_wellord2(A_7))
      | ~ r2_hidden(D_14,A_7)
      | ~ r2_hidden(C_13,A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [C_13,D_14,A_7] :
      ( r1_tarski(C_13,D_14)
      | ~ r2_hidden(k4_tarski(C_13,D_14),k1_wellord2(A_7))
      | ~ r2_hidden(D_14,A_7)
      | ~ r2_hidden(C_13,A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_717,plain,(
    ! [A_200,B_201,A_202] :
      ( r1_tarski('#skF_5'(A_200,B_201),'#skF_6'(A_200,B_201))
      | ~ r2_hidden('#skF_6'(A_200,B_201),A_202)
      | ~ r2_hidden('#skF_5'(A_200,B_201),A_202)
      | ~ r1_tarski(A_200,k1_wellord2(A_202))
      | r8_relat_2(A_200,B_201)
      | ~ v1_relat_1(A_200) ) ),
    inference(resolution,[status(thm)],[c_249,c_48])).

tff(c_764,plain,(
    ! [A_205,B_206,B_207] :
      ( r1_tarski('#skF_5'(A_205,B_206),'#skF_6'(A_205,B_206))
      | ~ r2_hidden('#skF_5'(A_205,B_206),B_207)
      | ~ r1_tarski(A_205,k1_wellord2(B_207))
      | ~ r1_tarski(B_206,B_207)
      | r8_relat_2(A_205,B_206)
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_108,c_717])).

tff(c_768,plain,(
    ! [A_15,B_29] :
      ( r1_tarski('#skF_5'(A_15,B_29),'#skF_6'(A_15,B_29))
      | ~ r1_tarski(A_15,k1_wellord2(B_29))
      | ~ r1_tarski(B_29,B_29)
      | r8_relat_2(A_15,B_29)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_40,c_764])).

tff(c_780,plain,(
    ! [A_212,B_213] :
      ( r1_tarski('#skF_5'(A_212,B_213),'#skF_6'(A_212,B_213))
      | ~ r1_tarski(A_212,k1_wellord2(B_213))
      | r8_relat_2(A_212,B_213)
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_768])).

tff(c_42,plain,(
    ! [A_15,B_29] :
      ( r2_hidden('#skF_4'(A_15,B_29),B_29)
      | r8_relat_2(A_15,B_29)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_5'(A_54,B_55),B_55)
      | r8_relat_2(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,(
    ! [A_54,B_55,B_2] :
      ( r2_hidden('#skF_5'(A_54,B_55),B_2)
      | ~ r1_tarski(B_55,B_2)
      | r8_relat_2(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_163,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(k4_tarski('#skF_4'(A_78,B_79),'#skF_5'(A_78,B_79)),A_78)
      | r8_relat_2(A_78,B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_258,plain,(
    ! [A_110,B_111,B_112] :
      ( r2_hidden(k4_tarski('#skF_4'(A_110,B_111),'#skF_5'(A_110,B_111)),B_112)
      | ~ r1_tarski(A_110,B_112)
      | r8_relat_2(A_110,B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_385,plain,(
    ! [A_143,B_144,A_145] :
      ( r1_tarski('#skF_4'(A_143,B_144),'#skF_5'(A_143,B_144))
      | ~ r2_hidden('#skF_5'(A_143,B_144),A_145)
      | ~ r2_hidden('#skF_4'(A_143,B_144),A_145)
      | ~ r1_tarski(A_143,k1_wellord2(A_145))
      | r8_relat_2(A_143,B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_258,c_48])).

tff(c_446,plain,(
    ! [A_150,B_151,B_152] :
      ( r1_tarski('#skF_4'(A_150,B_151),'#skF_5'(A_150,B_151))
      | ~ r2_hidden('#skF_4'(A_150,B_151),B_152)
      | ~ r1_tarski(A_150,k1_wellord2(B_152))
      | ~ r1_tarski(B_151,B_152)
      | r8_relat_2(A_150,B_151)
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_100,c_385])).

tff(c_450,plain,(
    ! [A_15,B_29] :
      ( r1_tarski('#skF_4'(A_15,B_29),'#skF_5'(A_15,B_29))
      | ~ r1_tarski(A_15,k1_wellord2(B_29))
      | ~ r1_tarski(B_29,B_29)
      | r8_relat_2(A_15,B_29)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_42,c_446])).

tff(c_455,plain,(
    ! [A_153,B_154] :
      ( r1_tarski('#skF_4'(A_153,B_154),'#skF_5'(A_153,B_154))
      | ~ r1_tarski(A_153,k1_wellord2(B_154))
      | r8_relat_2(A_153,B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_450])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_116,plain,(
    ! [A_60,B_61,B_2,B_62] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_2)
      | ~ r1_tarski(B_62,B_2)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_528,plain,(
    ! [A_163,B_164,A_165,B_166] :
      ( r2_hidden('#skF_1'(A_163,B_164),'#skF_5'(A_165,B_166))
      | ~ r1_tarski(A_163,'#skF_4'(A_165,B_166))
      | r1_tarski(A_163,B_164)
      | ~ r1_tarski(A_165,k1_wellord2(B_166))
      | r8_relat_2(A_165,B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_455,c_116])).

tff(c_537,plain,(
    ! [A_167,A_168,B_169] :
      ( ~ r1_tarski(A_167,'#skF_4'(A_168,B_169))
      | r1_tarski(A_167,'#skF_5'(A_168,B_169))
      | ~ r1_tarski(A_168,k1_wellord2(B_169))
      | r8_relat_2(A_168,B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_528,c_4])).

tff(c_540,plain,(
    ! [A_167,B_169] :
      ( ~ r1_tarski(A_167,'#skF_4'(k1_wellord2(B_169),B_169))
      | r1_tarski(A_167,'#skF_5'(k1_wellord2(B_169),B_169))
      | r8_relat_2(k1_wellord2(B_169),B_169)
      | ~ v1_relat_1(k1_wellord2(B_169)) ) ),
    inference(resolution,[status(thm)],[c_91,c_537])).

tff(c_544,plain,(
    ! [A_170,B_171] :
      ( ~ r1_tarski(A_170,'#skF_4'(k1_wellord2(B_171),B_171))
      | r1_tarski(A_170,'#skF_5'(k1_wellord2(B_171),B_171))
      | r8_relat_2(k1_wellord2(B_171),B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_540])).

tff(c_651,plain,(
    ! [A_184,B_185,B_186,A_187] :
      ( r2_hidden('#skF_1'(A_184,B_185),'#skF_5'(k1_wellord2(B_186),B_186))
      | ~ r1_tarski(A_184,A_187)
      | r1_tarski(A_184,B_185)
      | ~ r1_tarski(A_187,'#skF_4'(k1_wellord2(B_186),B_186))
      | r8_relat_2(k1_wellord2(B_186),B_186) ) ),
    inference(resolution,[status(thm)],[c_544,c_116])).

tff(c_691,plain,(
    ! [A_193,B_194,B_195] :
      ( r2_hidden('#skF_1'(A_193,B_194),'#skF_5'(k1_wellord2(B_195),B_195))
      | r1_tarski(A_193,B_194)
      | ~ r1_tarski(A_193,'#skF_4'(k1_wellord2(B_195),B_195))
      | r8_relat_2(k1_wellord2(B_195),B_195) ) ),
    inference(resolution,[status(thm)],[c_91,c_651])).

tff(c_698,plain,(
    ! [A_193,B_194,B_2,B_195] :
      ( r2_hidden('#skF_1'(A_193,B_194),B_2)
      | ~ r1_tarski('#skF_5'(k1_wellord2(B_195),B_195),B_2)
      | r1_tarski(A_193,B_194)
      | ~ r1_tarski(A_193,'#skF_4'(k1_wellord2(B_195),B_195))
      | r8_relat_2(k1_wellord2(B_195),B_195) ) ),
    inference(resolution,[status(thm)],[c_691,c_2])).

tff(c_783,plain,(
    ! [A_193,B_194,B_213] :
      ( r2_hidden('#skF_1'(A_193,B_194),'#skF_6'(k1_wellord2(B_213),B_213))
      | r1_tarski(A_193,B_194)
      | ~ r1_tarski(A_193,'#skF_4'(k1_wellord2(B_213),B_213))
      | ~ r1_tarski(k1_wellord2(B_213),k1_wellord2(B_213))
      | r8_relat_2(k1_wellord2(B_213),B_213)
      | ~ v1_relat_1(k1_wellord2(B_213)) ) ),
    inference(resolution,[status(thm)],[c_780,c_698])).

tff(c_894,plain,(
    ! [A_224,B_225,B_226] :
      ( r2_hidden('#skF_1'(A_224,B_225),'#skF_6'(k1_wellord2(B_226),B_226))
      | r1_tarski(A_224,B_225)
      | ~ r1_tarski(A_224,'#skF_4'(k1_wellord2(B_226),B_226))
      | r8_relat_2(k1_wellord2(B_226),B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91,c_783])).

tff(c_903,plain,(
    ! [A_227,B_228] :
      ( r1_tarski(A_227,'#skF_6'(k1_wellord2(B_228),B_228))
      | ~ r1_tarski(A_227,'#skF_4'(k1_wellord2(B_228),B_228))
      | r8_relat_2(k1_wellord2(B_228),B_228) ) ),
    inference(resolution,[status(thm)],[c_894,c_4])).

tff(c_26,plain,(
    ! [C_13,D_14,A_7] :
      ( r2_hidden(k4_tarski(C_13,D_14),k1_wellord2(A_7))
      | ~ r1_tarski(C_13,D_14)
      | ~ r2_hidden(D_14,A_7)
      | ~ r2_hidden(C_13,A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_186,plain,(
    ! [C_87,D_88,A_89] :
      ( r2_hidden(k4_tarski(C_87,D_88),k1_wellord2(A_89))
      | ~ r1_tarski(C_87,D_88)
      | ~ r2_hidden(D_88,A_89)
      | ~ r2_hidden(C_87,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_26])).

tff(c_32,plain,(
    ! [A_15,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_4'(A_15,B_29),'#skF_6'(A_15,B_29)),A_15)
      | r8_relat_2(A_15,B_29)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_193,plain,(
    ! [A_89,B_29] :
      ( r8_relat_2(k1_wellord2(A_89),B_29)
      | ~ v1_relat_1(k1_wellord2(A_89))
      | ~ r1_tarski('#skF_4'(k1_wellord2(A_89),B_29),'#skF_6'(k1_wellord2(A_89),B_29))
      | ~ r2_hidden('#skF_6'(k1_wellord2(A_89),B_29),A_89)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_89),B_29),A_89) ) ),
    inference(resolution,[status(thm)],[c_186,c_32])).

tff(c_199,plain,(
    ! [A_89,B_29] :
      ( r8_relat_2(k1_wellord2(A_89),B_29)
      | ~ r1_tarski('#skF_4'(k1_wellord2(A_89),B_29),'#skF_6'(k1_wellord2(A_89),B_29))
      | ~ r2_hidden('#skF_6'(k1_wellord2(A_89),B_29),A_89)
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_89),B_29),A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_193])).

tff(c_920,plain,(
    ! [B_228] :
      ( ~ r2_hidden('#skF_6'(k1_wellord2(B_228),B_228),B_228)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_228),B_228),B_228)
      | ~ r1_tarski('#skF_4'(k1_wellord2(B_228),B_228),'#skF_4'(k1_wellord2(B_228),B_228))
      | r8_relat_2(k1_wellord2(B_228),B_228) ) ),
    inference(resolution,[status(thm)],[c_903,c_199])).

tff(c_957,plain,(
    ! [B_229] :
      ( ~ r2_hidden('#skF_6'(k1_wellord2(B_229),B_229),B_229)
      | ~ r2_hidden('#skF_4'(k1_wellord2(B_229),B_229),B_229)
      | r8_relat_2(k1_wellord2(B_229),B_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_920])).

tff(c_961,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_2),B_2),B_2)
      | ~ r1_tarski(B_2,B_2)
      | r8_relat_2(k1_wellord2(B_2),B_2)
      | ~ v1_relat_1(k1_wellord2(B_2)) ) ),
    inference(resolution,[status(thm)],[c_108,c_957])).

tff(c_972,plain,(
    ! [B_230] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(B_230),B_230),B_230)
      | r8_relat_2(k1_wellord2(B_230),B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91,c_961])).

tff(c_976,plain,(
    ! [B_2] :
      ( ~ r1_tarski(B_2,B_2)
      | r8_relat_2(k1_wellord2(B_2),B_2)
      | ~ v1_relat_1(k1_wellord2(B_2)) ) ),
    inference(resolution,[status(thm)],[c_104,c_972])).

tff(c_983,plain,(
    ! [B_2] : r8_relat_2(k1_wellord2(B_2),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91,c_976])).

tff(c_24,plain,(
    ! [A_7] :
      ( k3_relat_1(k1_wellord2(A_7)) = A_7
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [A_7] : k3_relat_1(k1_wellord2(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24])).

tff(c_70,plain,(
    ! [A_44] :
      ( v8_relat_2(A_44)
      | ~ r8_relat_2(A_44,k3_relat_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_7] :
      ( v8_relat_2(k1_wellord2(A_7))
      | ~ r8_relat_2(k1_wellord2(A_7),A_7)
      | ~ v1_relat_1(k1_wellord2(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_70])).

tff(c_79,plain,(
    ! [A_7] :
      ( v8_relat_2(k1_wellord2(A_7))
      | ~ r8_relat_2(k1_wellord2(A_7),A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76])).

tff(c_995,plain,(
    ! [A_7] : v8_relat_2(k1_wellord2(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_79])).

tff(c_46,plain,(
    ~ v8_relat_2(k1_wellord2('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.55  
% 3.57/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.55  %$ r8_relat_2 > r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.57/1.55  
% 3.57/1.55  %Foreground sorts:
% 3.57/1.55  
% 3.57/1.55  
% 3.57/1.55  %Background operators:
% 3.57/1.55  
% 3.57/1.55  
% 3.57/1.55  %Foreground operators:
% 3.57/1.55  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.57/1.55  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.57/1.55  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.57/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.57/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.57/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.55  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.57/1.55  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 3.57/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.57/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.57/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.57/1.55  
% 3.57/1.57  tff(f_73, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.57/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.57/1.57  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (r8_relat_2(A, B) <=> (![C, D, E]: (((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(E, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, E), A)) => r2_hidden(k4_tarski(C, E), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 3.57/1.57  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.57/1.57  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> r8_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_2)).
% 3.57/1.57  tff(f_76, negated_conjecture, ~(![A]: v8_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_wellord2)).
% 3.57/1.57  tff(c_44, plain, (![A_39]: (v1_relat_1(k1_wellord2(A_39)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.57/1.57  tff(c_86, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_91, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_86, c_4])).
% 3.57/1.57  tff(c_101, plain, (![A_56, B_57]: (r2_hidden('#skF_4'(A_56, B_57), B_57) | r8_relat_2(A_56, B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_104, plain, (![A_56, B_57, B_2]: (r2_hidden('#skF_4'(A_56, B_57), B_2) | ~r1_tarski(B_57, B_2) | r8_relat_2(A_56, B_57) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_101, c_2])).
% 3.57/1.57  tff(c_105, plain, (![A_58, B_59]: (r2_hidden('#skF_6'(A_58, B_59), B_59) | r8_relat_2(A_58, B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_108, plain, (![A_58, B_59, B_2]: (r2_hidden('#skF_6'(A_58, B_59), B_2) | ~r1_tarski(B_59, B_2) | r8_relat_2(A_58, B_59) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_105, c_2])).
% 3.57/1.57  tff(c_40, plain, (![A_15, B_29]: (r2_hidden('#skF_5'(A_15, B_29), B_29) | r8_relat_2(A_15, B_29) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_154, plain, (![A_71, B_72]: (r2_hidden(k4_tarski('#skF_5'(A_71, B_72), '#skF_6'(A_71, B_72)), A_71) | r8_relat_2(A_71, B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_249, plain, (![A_107, B_108, B_109]: (r2_hidden(k4_tarski('#skF_5'(A_107, B_108), '#skF_6'(A_107, B_108)), B_109) | ~r1_tarski(A_107, B_109) | r8_relat_2(A_107, B_108) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_154, c_2])).
% 3.57/1.57  tff(c_28, plain, (![C_13, D_14, A_7]: (r1_tarski(C_13, D_14) | ~r2_hidden(k4_tarski(C_13, D_14), k1_wellord2(A_7)) | ~r2_hidden(D_14, A_7) | ~r2_hidden(C_13, A_7) | ~v1_relat_1(k1_wellord2(A_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.57  tff(c_48, plain, (![C_13, D_14, A_7]: (r1_tarski(C_13, D_14) | ~r2_hidden(k4_tarski(C_13, D_14), k1_wellord2(A_7)) | ~r2_hidden(D_14, A_7) | ~r2_hidden(C_13, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 3.57/1.57  tff(c_717, plain, (![A_200, B_201, A_202]: (r1_tarski('#skF_5'(A_200, B_201), '#skF_6'(A_200, B_201)) | ~r2_hidden('#skF_6'(A_200, B_201), A_202) | ~r2_hidden('#skF_5'(A_200, B_201), A_202) | ~r1_tarski(A_200, k1_wellord2(A_202)) | r8_relat_2(A_200, B_201) | ~v1_relat_1(A_200))), inference(resolution, [status(thm)], [c_249, c_48])).
% 3.57/1.57  tff(c_764, plain, (![A_205, B_206, B_207]: (r1_tarski('#skF_5'(A_205, B_206), '#skF_6'(A_205, B_206)) | ~r2_hidden('#skF_5'(A_205, B_206), B_207) | ~r1_tarski(A_205, k1_wellord2(B_207)) | ~r1_tarski(B_206, B_207) | r8_relat_2(A_205, B_206) | ~v1_relat_1(A_205))), inference(resolution, [status(thm)], [c_108, c_717])).
% 3.57/1.57  tff(c_768, plain, (![A_15, B_29]: (r1_tarski('#skF_5'(A_15, B_29), '#skF_6'(A_15, B_29)) | ~r1_tarski(A_15, k1_wellord2(B_29)) | ~r1_tarski(B_29, B_29) | r8_relat_2(A_15, B_29) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_40, c_764])).
% 3.57/1.57  tff(c_780, plain, (![A_212, B_213]: (r1_tarski('#skF_5'(A_212, B_213), '#skF_6'(A_212, B_213)) | ~r1_tarski(A_212, k1_wellord2(B_213)) | r8_relat_2(A_212, B_213) | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_768])).
% 3.57/1.57  tff(c_42, plain, (![A_15, B_29]: (r2_hidden('#skF_4'(A_15, B_29), B_29) | r8_relat_2(A_15, B_29) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_97, plain, (![A_54, B_55]: (r2_hidden('#skF_5'(A_54, B_55), B_55) | r8_relat_2(A_54, B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_100, plain, (![A_54, B_55, B_2]: (r2_hidden('#skF_5'(A_54, B_55), B_2) | ~r1_tarski(B_55, B_2) | r8_relat_2(A_54, B_55) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_97, c_2])).
% 3.57/1.57  tff(c_163, plain, (![A_78, B_79]: (r2_hidden(k4_tarski('#skF_4'(A_78, B_79), '#skF_5'(A_78, B_79)), A_78) | r8_relat_2(A_78, B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_258, plain, (![A_110, B_111, B_112]: (r2_hidden(k4_tarski('#skF_4'(A_110, B_111), '#skF_5'(A_110, B_111)), B_112) | ~r1_tarski(A_110, B_112) | r8_relat_2(A_110, B_111) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_163, c_2])).
% 3.57/1.57  tff(c_385, plain, (![A_143, B_144, A_145]: (r1_tarski('#skF_4'(A_143, B_144), '#skF_5'(A_143, B_144)) | ~r2_hidden('#skF_5'(A_143, B_144), A_145) | ~r2_hidden('#skF_4'(A_143, B_144), A_145) | ~r1_tarski(A_143, k1_wellord2(A_145)) | r8_relat_2(A_143, B_144) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_258, c_48])).
% 3.57/1.57  tff(c_446, plain, (![A_150, B_151, B_152]: (r1_tarski('#skF_4'(A_150, B_151), '#skF_5'(A_150, B_151)) | ~r2_hidden('#skF_4'(A_150, B_151), B_152) | ~r1_tarski(A_150, k1_wellord2(B_152)) | ~r1_tarski(B_151, B_152) | r8_relat_2(A_150, B_151) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_100, c_385])).
% 3.57/1.57  tff(c_450, plain, (![A_15, B_29]: (r1_tarski('#skF_4'(A_15, B_29), '#skF_5'(A_15, B_29)) | ~r1_tarski(A_15, k1_wellord2(B_29)) | ~r1_tarski(B_29, B_29) | r8_relat_2(A_15, B_29) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_42, c_446])).
% 3.57/1.57  tff(c_455, plain, (![A_153, B_154]: (r1_tarski('#skF_4'(A_153, B_154), '#skF_5'(A_153, B_154)) | ~r1_tarski(A_153, k1_wellord2(B_154)) | r8_relat_2(A_153, B_154) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_450])).
% 3.57/1.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_92, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.57/1.57  tff(c_109, plain, (![A_60, B_61, B_62]: (r2_hidden('#skF_1'(A_60, B_61), B_62) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_6, c_92])).
% 3.57/1.57  tff(c_116, plain, (![A_60, B_61, B_2, B_62]: (r2_hidden('#skF_1'(A_60, B_61), B_2) | ~r1_tarski(B_62, B_2) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_109, c_2])).
% 3.57/1.57  tff(c_528, plain, (![A_163, B_164, A_165, B_166]: (r2_hidden('#skF_1'(A_163, B_164), '#skF_5'(A_165, B_166)) | ~r1_tarski(A_163, '#skF_4'(A_165, B_166)) | r1_tarski(A_163, B_164) | ~r1_tarski(A_165, k1_wellord2(B_166)) | r8_relat_2(A_165, B_166) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_455, c_116])).
% 3.57/1.57  tff(c_537, plain, (![A_167, A_168, B_169]: (~r1_tarski(A_167, '#skF_4'(A_168, B_169)) | r1_tarski(A_167, '#skF_5'(A_168, B_169)) | ~r1_tarski(A_168, k1_wellord2(B_169)) | r8_relat_2(A_168, B_169) | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_528, c_4])).
% 3.57/1.57  tff(c_540, plain, (![A_167, B_169]: (~r1_tarski(A_167, '#skF_4'(k1_wellord2(B_169), B_169)) | r1_tarski(A_167, '#skF_5'(k1_wellord2(B_169), B_169)) | r8_relat_2(k1_wellord2(B_169), B_169) | ~v1_relat_1(k1_wellord2(B_169)))), inference(resolution, [status(thm)], [c_91, c_537])).
% 3.57/1.57  tff(c_544, plain, (![A_170, B_171]: (~r1_tarski(A_170, '#skF_4'(k1_wellord2(B_171), B_171)) | r1_tarski(A_170, '#skF_5'(k1_wellord2(B_171), B_171)) | r8_relat_2(k1_wellord2(B_171), B_171))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_540])).
% 3.57/1.57  tff(c_651, plain, (![A_184, B_185, B_186, A_187]: (r2_hidden('#skF_1'(A_184, B_185), '#skF_5'(k1_wellord2(B_186), B_186)) | ~r1_tarski(A_184, A_187) | r1_tarski(A_184, B_185) | ~r1_tarski(A_187, '#skF_4'(k1_wellord2(B_186), B_186)) | r8_relat_2(k1_wellord2(B_186), B_186))), inference(resolution, [status(thm)], [c_544, c_116])).
% 3.57/1.57  tff(c_691, plain, (![A_193, B_194, B_195]: (r2_hidden('#skF_1'(A_193, B_194), '#skF_5'(k1_wellord2(B_195), B_195)) | r1_tarski(A_193, B_194) | ~r1_tarski(A_193, '#skF_4'(k1_wellord2(B_195), B_195)) | r8_relat_2(k1_wellord2(B_195), B_195))), inference(resolution, [status(thm)], [c_91, c_651])).
% 3.57/1.57  tff(c_698, plain, (![A_193, B_194, B_2, B_195]: (r2_hidden('#skF_1'(A_193, B_194), B_2) | ~r1_tarski('#skF_5'(k1_wellord2(B_195), B_195), B_2) | r1_tarski(A_193, B_194) | ~r1_tarski(A_193, '#skF_4'(k1_wellord2(B_195), B_195)) | r8_relat_2(k1_wellord2(B_195), B_195))), inference(resolution, [status(thm)], [c_691, c_2])).
% 3.57/1.57  tff(c_783, plain, (![A_193, B_194, B_213]: (r2_hidden('#skF_1'(A_193, B_194), '#skF_6'(k1_wellord2(B_213), B_213)) | r1_tarski(A_193, B_194) | ~r1_tarski(A_193, '#skF_4'(k1_wellord2(B_213), B_213)) | ~r1_tarski(k1_wellord2(B_213), k1_wellord2(B_213)) | r8_relat_2(k1_wellord2(B_213), B_213) | ~v1_relat_1(k1_wellord2(B_213)))), inference(resolution, [status(thm)], [c_780, c_698])).
% 3.57/1.57  tff(c_894, plain, (![A_224, B_225, B_226]: (r2_hidden('#skF_1'(A_224, B_225), '#skF_6'(k1_wellord2(B_226), B_226)) | r1_tarski(A_224, B_225) | ~r1_tarski(A_224, '#skF_4'(k1_wellord2(B_226), B_226)) | r8_relat_2(k1_wellord2(B_226), B_226))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91, c_783])).
% 3.57/1.57  tff(c_903, plain, (![A_227, B_228]: (r1_tarski(A_227, '#skF_6'(k1_wellord2(B_228), B_228)) | ~r1_tarski(A_227, '#skF_4'(k1_wellord2(B_228), B_228)) | r8_relat_2(k1_wellord2(B_228), B_228))), inference(resolution, [status(thm)], [c_894, c_4])).
% 3.57/1.57  tff(c_26, plain, (![C_13, D_14, A_7]: (r2_hidden(k4_tarski(C_13, D_14), k1_wellord2(A_7)) | ~r1_tarski(C_13, D_14) | ~r2_hidden(D_14, A_7) | ~r2_hidden(C_13, A_7) | ~v1_relat_1(k1_wellord2(A_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.57  tff(c_186, plain, (![C_87, D_88, A_89]: (r2_hidden(k4_tarski(C_87, D_88), k1_wellord2(A_89)) | ~r1_tarski(C_87, D_88) | ~r2_hidden(D_88, A_89) | ~r2_hidden(C_87, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_26])).
% 3.57/1.57  tff(c_32, plain, (![A_15, B_29]: (~r2_hidden(k4_tarski('#skF_4'(A_15, B_29), '#skF_6'(A_15, B_29)), A_15) | r8_relat_2(A_15, B_29) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.57  tff(c_193, plain, (![A_89, B_29]: (r8_relat_2(k1_wellord2(A_89), B_29) | ~v1_relat_1(k1_wellord2(A_89)) | ~r1_tarski('#skF_4'(k1_wellord2(A_89), B_29), '#skF_6'(k1_wellord2(A_89), B_29)) | ~r2_hidden('#skF_6'(k1_wellord2(A_89), B_29), A_89) | ~r2_hidden('#skF_4'(k1_wellord2(A_89), B_29), A_89))), inference(resolution, [status(thm)], [c_186, c_32])).
% 3.57/1.57  tff(c_199, plain, (![A_89, B_29]: (r8_relat_2(k1_wellord2(A_89), B_29) | ~r1_tarski('#skF_4'(k1_wellord2(A_89), B_29), '#skF_6'(k1_wellord2(A_89), B_29)) | ~r2_hidden('#skF_6'(k1_wellord2(A_89), B_29), A_89) | ~r2_hidden('#skF_4'(k1_wellord2(A_89), B_29), A_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_193])).
% 3.57/1.57  tff(c_920, plain, (![B_228]: (~r2_hidden('#skF_6'(k1_wellord2(B_228), B_228), B_228) | ~r2_hidden('#skF_4'(k1_wellord2(B_228), B_228), B_228) | ~r1_tarski('#skF_4'(k1_wellord2(B_228), B_228), '#skF_4'(k1_wellord2(B_228), B_228)) | r8_relat_2(k1_wellord2(B_228), B_228))), inference(resolution, [status(thm)], [c_903, c_199])).
% 3.57/1.57  tff(c_957, plain, (![B_229]: (~r2_hidden('#skF_6'(k1_wellord2(B_229), B_229), B_229) | ~r2_hidden('#skF_4'(k1_wellord2(B_229), B_229), B_229) | r8_relat_2(k1_wellord2(B_229), B_229))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_920])).
% 3.57/1.57  tff(c_961, plain, (![B_2]: (~r2_hidden('#skF_4'(k1_wellord2(B_2), B_2), B_2) | ~r1_tarski(B_2, B_2) | r8_relat_2(k1_wellord2(B_2), B_2) | ~v1_relat_1(k1_wellord2(B_2)))), inference(resolution, [status(thm)], [c_108, c_957])).
% 3.57/1.57  tff(c_972, plain, (![B_230]: (~r2_hidden('#skF_4'(k1_wellord2(B_230), B_230), B_230) | r8_relat_2(k1_wellord2(B_230), B_230))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91, c_961])).
% 3.57/1.57  tff(c_976, plain, (![B_2]: (~r1_tarski(B_2, B_2) | r8_relat_2(k1_wellord2(B_2), B_2) | ~v1_relat_1(k1_wellord2(B_2)))), inference(resolution, [status(thm)], [c_104, c_972])).
% 3.57/1.57  tff(c_983, plain, (![B_2]: (r8_relat_2(k1_wellord2(B_2), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91, c_976])).
% 3.57/1.57  tff(c_24, plain, (![A_7]: (k3_relat_1(k1_wellord2(A_7))=A_7 | ~v1_relat_1(k1_wellord2(A_7)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.57/1.57  tff(c_52, plain, (![A_7]: (k3_relat_1(k1_wellord2(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24])).
% 3.57/1.57  tff(c_70, plain, (![A_44]: (v8_relat_2(A_44) | ~r8_relat_2(A_44, k3_relat_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.57  tff(c_76, plain, (![A_7]: (v8_relat_2(k1_wellord2(A_7)) | ~r8_relat_2(k1_wellord2(A_7), A_7) | ~v1_relat_1(k1_wellord2(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_70])).
% 3.57/1.57  tff(c_79, plain, (![A_7]: (v8_relat_2(k1_wellord2(A_7)) | ~r8_relat_2(k1_wellord2(A_7), A_7))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76])).
% 3.57/1.57  tff(c_995, plain, (![A_7]: (v8_relat_2(k1_wellord2(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_79])).
% 3.57/1.57  tff(c_46, plain, (~v8_relat_2(k1_wellord2('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.57/1.57  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_995, c_46])).
% 3.57/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.57  
% 3.57/1.57  Inference rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Ref     : 0
% 3.57/1.57  #Sup     : 237
% 3.57/1.57  #Fact    : 0
% 3.57/1.57  #Define  : 0
% 3.57/1.57  #Split   : 0
% 3.57/1.57  #Chain   : 0
% 3.57/1.57  #Close   : 0
% 3.57/1.57  
% 3.57/1.57  Ordering : KBO
% 3.57/1.57  
% 3.57/1.57  Simplification rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Subsume      : 19
% 3.57/1.57  #Demod        : 111
% 3.57/1.57  #Tautology    : 35
% 3.57/1.57  #SimpNegUnit  : 0
% 3.57/1.57  #BackRed      : 2
% 3.57/1.57  
% 3.57/1.57  #Partial instantiations: 0
% 3.57/1.57  #Strategies tried      : 1
% 3.57/1.57  
% 3.57/1.57  Timing (in seconds)
% 3.57/1.57  ----------------------
% 3.57/1.57  Preprocessing        : 0.30
% 3.57/1.57  Parsing              : 0.16
% 3.57/1.57  CNF conversion       : 0.02
% 3.57/1.57  Main loop            : 0.51
% 3.57/1.57  Inferencing          : 0.17
% 3.57/1.57  Reduction            : 0.13
% 3.57/1.57  Demodulation         : 0.09
% 3.57/1.57  BG Simplification    : 0.03
% 3.57/1.57  Subsumption          : 0.15
% 3.57/1.57  Abstraction          : 0.02
% 3.57/1.57  MUC search           : 0.00
% 3.57/1.57  Cooper               : 0.00
% 3.57/1.57  Total                : 0.84
% 3.57/1.57  Index Insertion      : 0.00
% 3.57/1.57  Index Deletion       : 0.00
% 3.57/1.57  Index Matching       : 0.00
% 3.57/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
