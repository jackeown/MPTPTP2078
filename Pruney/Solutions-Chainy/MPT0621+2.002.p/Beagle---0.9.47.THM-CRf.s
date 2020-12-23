%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :  101 (1157 expanded)
%              Number of leaves         :   30 ( 424 expanded)
%              Depth                    :   15
%              Number of atoms          :  198 (3598 expanded)
%              Number of equality atoms :   85 (1404 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_85,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_50,plain,(
    ! [A_54] : v1_funct_1('#skF_6'(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ! [A_54] : k1_relat_1('#skF_6'(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    ! [A_54] : v1_relat_1('#skF_6'(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    ! [A_47,B_48] : k1_relat_1('#skF_5'(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_47,B_48] : v1_funct_1('#skF_5'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_47,B_48] : v1_relat_1('#skF_5'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_90,plain,(
    ! [C_72,B_73] :
      ( C_72 = B_73
      | k1_relat_1(C_72) != '#skF_7'
      | k1_relat_1(B_73) != '#skF_7'
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_95,plain,(
    ! [B_73,A_47,B_48] :
      ( B_73 = '#skF_5'(A_47,B_48)
      | k1_relat_1('#skF_5'(A_47,B_48)) != '#skF_7'
      | k1_relat_1(B_73) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_47,B_48))
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_132,plain,(
    ! [B_73,A_47,B_48] :
      ( B_73 = '#skF_5'(A_47,B_48)
      | k1_relat_1('#skF_5'(A_47,B_48)) != '#skF_7'
      | k1_relat_1(B_73) != '#skF_7'
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_95])).

tff(c_174,plain,(
    ! [B_94,A_95,B_96] :
      ( B_94 = '#skF_5'(A_95,B_96)
      | A_95 != '#skF_7'
      | k1_relat_1(B_94) != '#skF_7'
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_132])).

tff(c_180,plain,(
    ! [A_54,A_95,B_96] :
      ( '#skF_6'(A_54) = '#skF_5'(A_95,B_96)
      | A_95 != '#skF_7'
      | k1_relat_1('#skF_6'(A_54)) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_54)) ) ),
    inference(resolution,[status(thm)],[c_52,c_174])).

tff(c_189,plain,(
    ! [A_54,A_95,B_96] :
      ( '#skF_6'(A_54) = '#skF_5'(A_95,B_96)
      | A_95 != '#skF_7'
      | A_54 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_180])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_79,B_80] : ~ r2_hidden(A_79,k2_zfmisc_1(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_123])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_99,plain,(
    ! [A_74] :
      ( v1_relat_1(A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_109,plain,(
    ! [A_77] :
      ( v1_funct_1(A_77)
      | ~ v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_903,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_2'(A_161,B_162),k1_relat_1(A_161))
      | r2_hidden('#skF_3'(A_161,B_162),B_162)
      | k2_relat_1(A_161) = B_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_975,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_162),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_162),B_162)
      | k2_relat_1(k1_xboole_0) = B_162
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_903])).

tff(c_1004,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_162),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_162),B_162)
      | k1_xboole_0 = B_162 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_113,c_14,c_975])).

tff(c_1006,plain,(
    ! [B_163] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_163),B_163)
      | k1_xboole_0 = B_163 ) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1004])).

tff(c_38,plain,(
    ! [A_47,B_48,D_53] :
      ( k1_funct_1('#skF_5'(A_47,B_48),D_53) = B_48
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_190,plain,(
    ! [A_97,D_98] :
      ( r2_hidden(k1_funct_1(A_97,D_98),k2_relat_1(A_97))
      | ~ r2_hidden(D_98,k1_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    ! [B_48,A_47,D_53] :
      ( r2_hidden(B_48,k2_relat_1('#skF_5'(A_47,B_48)))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_5'(A_47,B_48)))
      | ~ v1_funct_1('#skF_5'(A_47,B_48))
      | ~ v1_relat_1('#skF_5'(A_47,B_48))
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_190])).

tff(c_201,plain,(
    ! [B_48,A_47,D_53] :
      ( r2_hidden(B_48,k2_relat_1('#skF_5'(A_47,B_48)))
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_193])).

tff(c_1183,plain,(
    ! [B_165,B_166] :
      ( r2_hidden(B_165,k2_relat_1('#skF_5'(B_166,B_165)))
      | k1_xboole_0 = B_166 ) ),
    inference(resolution,[status(thm)],[c_1006,c_201])).

tff(c_1204,plain,(
    ! [B_96,A_54,A_95] :
      ( r2_hidden(B_96,k2_relat_1('#skF_6'(A_54)))
      | k1_xboole_0 = A_95
      | A_95 != '#skF_7'
      | A_54 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1183])).

tff(c_1406,plain,(
    ! [B_96,A_54] :
      ( r2_hidden(B_96,k2_relat_1('#skF_6'(A_54)))
      | A_54 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_479,plain,(
    ! [A_135,C_136] :
      ( r2_hidden('#skF_4'(A_135,k2_relat_1(A_135),C_136),k1_relat_1(A_135))
      | ~ r2_hidden(C_136,k2_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_497,plain,(
    ! [A_54,C_136] :
      ( r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_136),A_54)
      | ~ r2_hidden(C_136,k2_relat_1('#skF_6'(A_54)))
      | ~ v1_funct_1('#skF_6'(A_54))
      | ~ v1_relat_1('#skF_6'(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_479])).

tff(c_513,plain,(
    ! [A_54,C_136] :
      ( r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_136),A_54)
      | ~ r2_hidden(C_136,k2_relat_1('#skF_6'(A_54))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_497])).

tff(c_46,plain,(
    ! [A_54,C_59] :
      ( k1_funct_1('#skF_6'(A_54),C_59) = np__1
      | ~ r2_hidden(C_59,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_411,plain,(
    ! [A_120,C_121] :
      ( k1_funct_1(A_120,'#skF_4'(A_120,k2_relat_1(A_120),C_121)) = C_121
      | ~ r2_hidden(C_121,k2_relat_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_436,plain,(
    ! [C_121,A_54] :
      ( np__1 = C_121
      | ~ r2_hidden(C_121,k2_relat_1('#skF_6'(A_54)))
      | ~ v1_funct_1('#skF_6'(A_54))
      | ~ v1_relat_1('#skF_6'(A_54))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_121),A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_411])).

tff(c_2262,plain,(
    ! [C_210,A_211] :
      ( np__1 = C_210
      | ~ r2_hidden(C_210,k2_relat_1('#skF_6'(A_211)))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_211),k2_relat_1('#skF_6'(A_211)),C_210),A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_436])).

tff(c_2313,plain,(
    ! [C_213,A_214] :
      ( np__1 = C_213
      | ~ r2_hidden(C_213,k2_relat_1('#skF_6'(A_214))) ) ),
    inference(resolution,[status(thm)],[c_513,c_2262])).

tff(c_2385,plain,(
    ! [B_96,A_54] :
      ( np__1 = B_96
      | A_54 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1406,c_2313])).

tff(c_2400,plain,(
    ! [A_54] : A_54 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2385])).

tff(c_2405,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2400])).

tff(c_2408,plain,(
    np__1 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2385])).

tff(c_2406,plain,(
    ! [B_96] : np__1 = B_96 ),
    inference(splitRight,[status(thm)],[c_2385])).

tff(c_2736,plain,(
    ! [B_1526] : B_1526 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2408,c_2406])).

tff(c_1408,plain,(
    ! [B_171,A_172] :
      ( r2_hidden(B_171,k2_relat_1('#skF_6'(A_172)))
      | A_172 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_1204])).

tff(c_527,plain,(
    ! [A_140,C_141] :
      ( r2_hidden('#skF_4'('#skF_6'(A_140),k2_relat_1('#skF_6'(A_140)),C_141),A_140)
      | ~ r2_hidden(C_141,k2_relat_1('#skF_6'(A_140))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_497])).

tff(c_196,plain,(
    ! [A_54,C_59] :
      ( r2_hidden(np__1,k2_relat_1('#skF_6'(A_54)))
      | ~ r2_hidden(C_59,k1_relat_1('#skF_6'(A_54)))
      | ~ v1_funct_1('#skF_6'(A_54))
      | ~ v1_relat_1('#skF_6'(A_54))
      | ~ r2_hidden(C_59,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_190])).

tff(c_203,plain,(
    ! [A_54,C_59] :
      ( r2_hidden(np__1,k2_relat_1('#skF_6'(A_54)))
      | ~ r2_hidden(C_59,A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_196])).

tff(c_657,plain,(
    ! [A_145,C_146] :
      ( r2_hidden(np__1,k2_relat_1('#skF_6'(A_145)))
      | ~ r2_hidden(C_146,k2_relat_1('#skF_6'(A_145))) ) ),
    inference(resolution,[status(thm)],[c_527,c_203])).

tff(c_670,plain,(
    ! [A_145,C_136] :
      ( r2_hidden(np__1,k2_relat_1('#skF_6'(A_145)))
      | ~ r2_hidden(C_136,k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(A_145))))) ) ),
    inference(resolution,[status(thm)],[c_513,c_657])).

tff(c_1487,plain,(
    ! [A_175] :
      ( r2_hidden(np__1,k2_relat_1('#skF_6'(A_175)))
      | k2_relat_1('#skF_6'(A_175)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1408,c_670])).

tff(c_216,plain,(
    ! [A_104,A_105,B_106] :
      ( '#skF_6'(A_104) = '#skF_5'(A_105,B_106)
      | A_105 != '#skF_7'
      | A_104 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_180])).

tff(c_225,plain,(
    ! [A_104,D_53,B_106,A_105] :
      ( k1_funct_1('#skF_6'(A_104),D_53) = B_106
      | ~ r2_hidden(D_53,A_105)
      | A_105 != '#skF_7'
      | A_104 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_38])).

tff(c_1533,plain,(
    ! [A_104,B_106,A_175] :
      ( k1_funct_1('#skF_6'(A_104),np__1) = B_106
      | A_104 != '#skF_7'
      | k2_relat_1('#skF_6'(A_175)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1487,c_225])).

tff(c_2261,plain,(
    ! [A_175] : k2_relat_1('#skF_6'(A_175)) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1533])).

tff(c_3031,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2736,c_2261])).

tff(c_3059,plain,(
    ! [A_2841] :
      ( k1_funct_1('#skF_6'(A_2841),np__1) = k1_xboole_0
      | A_2841 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_1533])).

tff(c_3032,plain,(
    ! [A_104,B_106] :
      ( k1_funct_1('#skF_6'(A_104),np__1) = B_106
      | A_104 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_1533])).

tff(c_3062,plain,(
    ! [B_106,A_2841] :
      ( k1_xboole_0 = B_106
      | A_2841 != '#skF_7'
      | A_2841 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3059,c_3032])).

tff(c_3681,plain,(
    ! [A_2841] :
      ( A_2841 != '#skF_7'
      | A_2841 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_3062])).

tff(c_3735,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3681])).

tff(c_3738,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3062])).

tff(c_3736,plain,(
    ! [B_106] : k1_xboole_0 = B_106 ),
    inference(splitRight,[status(thm)],[c_3062])).

tff(c_3961,plain,(
    ! [B_5222] : B_5222 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_3738,c_3736])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4177,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3961,c_54])).

tff(c_4180,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1204])).

tff(c_4198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4180,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.28/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.96  
% 5.28/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.96  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 5.28/1.96  
% 5.28/1.96  %Foreground sorts:
% 5.28/1.96  
% 5.28/1.96  
% 5.28/1.96  %Background operators:
% 5.28/1.96  
% 5.28/1.96  
% 5.28/1.96  %Foreground operators:
% 5.28/1.96  tff(np__1, type, np__1: $i).
% 5.28/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.28/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.28/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.28/1.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.28/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.28/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.28/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.28/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.28/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.28/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.28/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.28/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.28/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.28/1.96  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.28/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.28/1.96  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.28/1.96  
% 5.28/1.98  tff(f_85, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 5.28/1.98  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 5.28/1.98  tff(f_104, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 5.28/1.98  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.28/1.98  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.28/1.98  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.28/1.98  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.28/1.98  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.28/1.98  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.28/1.98  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.28/1.98  tff(c_50, plain, (![A_54]: (v1_funct_1('#skF_6'(A_54)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.98  tff(c_48, plain, (![A_54]: (k1_relat_1('#skF_6'(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.98  tff(c_52, plain, (![A_54]: (v1_relat_1('#skF_6'(A_54)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.98  tff(c_40, plain, (![A_47, B_48]: (k1_relat_1('#skF_5'(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.28/1.98  tff(c_42, plain, (![A_47, B_48]: (v1_funct_1('#skF_5'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.28/1.98  tff(c_44, plain, (![A_47, B_48]: (v1_relat_1('#skF_5'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.28/1.98  tff(c_90, plain, (![C_72, B_73]: (C_72=B_73 | k1_relat_1(C_72)!='#skF_7' | k1_relat_1(B_73)!='#skF_7' | ~v1_funct_1(C_72) | ~v1_relat_1(C_72) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/1.98  tff(c_95, plain, (![B_73, A_47, B_48]: (B_73='#skF_5'(A_47, B_48) | k1_relat_1('#skF_5'(A_47, B_48))!='#skF_7' | k1_relat_1(B_73)!='#skF_7' | ~v1_funct_1('#skF_5'(A_47, B_48)) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_44, c_90])).
% 5.28/1.98  tff(c_132, plain, (![B_73, A_47, B_48]: (B_73='#skF_5'(A_47, B_48) | k1_relat_1('#skF_5'(A_47, B_48))!='#skF_7' | k1_relat_1(B_73)!='#skF_7' | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95])).
% 5.28/1.98  tff(c_174, plain, (![B_94, A_95, B_96]: (B_94='#skF_5'(A_95, B_96) | A_95!='#skF_7' | k1_relat_1(B_94)!='#skF_7' | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_132])).
% 5.28/1.98  tff(c_180, plain, (![A_54, A_95, B_96]: ('#skF_6'(A_54)='#skF_5'(A_95, B_96) | A_95!='#skF_7' | k1_relat_1('#skF_6'(A_54))!='#skF_7' | ~v1_funct_1('#skF_6'(A_54)))), inference(resolution, [status(thm)], [c_52, c_174])).
% 5.28/1.98  tff(c_189, plain, (![A_54, A_95, B_96]: ('#skF_6'(A_54)='#skF_5'(A_95, B_96) | A_95!='#skF_7' | A_54!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_180])).
% 5.28/1.98  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.28/1.98  tff(c_123, plain, (![A_79, B_80]: (~r2_hidden(A_79, k2_zfmisc_1(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.28/1.98  tff(c_129, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_123])).
% 5.28/1.98  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.28/1.98  tff(c_99, plain, (![A_74]: (v1_relat_1(A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.28/1.98  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_99])).
% 5.28/1.98  tff(c_109, plain, (![A_77]: (v1_funct_1(A_77) | ~v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.28/1.98  tff(c_113, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_109])).
% 5.28/1.98  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.28/1.98  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.28/1.98  tff(c_903, plain, (![A_161, B_162]: (r2_hidden('#skF_2'(A_161, B_162), k1_relat_1(A_161)) | r2_hidden('#skF_3'(A_161, B_162), B_162) | k2_relat_1(A_161)=B_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/1.98  tff(c_975, plain, (![B_162]: (r2_hidden('#skF_2'(k1_xboole_0, B_162), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_162), B_162) | k2_relat_1(k1_xboole_0)=B_162 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_903])).
% 5.28/1.98  tff(c_1004, plain, (![B_162]: (r2_hidden('#skF_2'(k1_xboole_0, B_162), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_162), B_162) | k1_xboole_0=B_162)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_113, c_14, c_975])).
% 5.28/1.98  tff(c_1006, plain, (![B_163]: (r2_hidden('#skF_3'(k1_xboole_0, B_163), B_163) | k1_xboole_0=B_163)), inference(negUnitSimplification, [status(thm)], [c_129, c_1004])).
% 5.28/1.98  tff(c_38, plain, (![A_47, B_48, D_53]: (k1_funct_1('#skF_5'(A_47, B_48), D_53)=B_48 | ~r2_hidden(D_53, A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.28/1.98  tff(c_190, plain, (![A_97, D_98]: (r2_hidden(k1_funct_1(A_97, D_98), k2_relat_1(A_97)) | ~r2_hidden(D_98, k1_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/1.98  tff(c_193, plain, (![B_48, A_47, D_53]: (r2_hidden(B_48, k2_relat_1('#skF_5'(A_47, B_48))) | ~r2_hidden(D_53, k1_relat_1('#skF_5'(A_47, B_48))) | ~v1_funct_1('#skF_5'(A_47, B_48)) | ~v1_relat_1('#skF_5'(A_47, B_48)) | ~r2_hidden(D_53, A_47))), inference(superposition, [status(thm), theory('equality')], [c_38, c_190])).
% 5.28/1.98  tff(c_201, plain, (![B_48, A_47, D_53]: (r2_hidden(B_48, k2_relat_1('#skF_5'(A_47, B_48))) | ~r2_hidden(D_53, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_193])).
% 5.28/1.98  tff(c_1183, plain, (![B_165, B_166]: (r2_hidden(B_165, k2_relat_1('#skF_5'(B_166, B_165))) | k1_xboole_0=B_166)), inference(resolution, [status(thm)], [c_1006, c_201])).
% 5.28/1.98  tff(c_1204, plain, (![B_96, A_54, A_95]: (r2_hidden(B_96, k2_relat_1('#skF_6'(A_54))) | k1_xboole_0=A_95 | A_95!='#skF_7' | A_54!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_189, c_1183])).
% 5.28/1.98  tff(c_1406, plain, (![B_96, A_54]: (r2_hidden(B_96, k2_relat_1('#skF_6'(A_54))) | A_54!='#skF_7')), inference(splitLeft, [status(thm)], [c_1204])).
% 5.28/1.98  tff(c_479, plain, (![A_135, C_136]: (r2_hidden('#skF_4'(A_135, k2_relat_1(A_135), C_136), k1_relat_1(A_135)) | ~r2_hidden(C_136, k2_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/1.98  tff(c_497, plain, (![A_54, C_136]: (r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_136), A_54) | ~r2_hidden(C_136, k2_relat_1('#skF_6'(A_54))) | ~v1_funct_1('#skF_6'(A_54)) | ~v1_relat_1('#skF_6'(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_479])).
% 5.28/1.98  tff(c_513, plain, (![A_54, C_136]: (r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_136), A_54) | ~r2_hidden(C_136, k2_relat_1('#skF_6'(A_54))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_497])).
% 5.28/1.98  tff(c_46, plain, (![A_54, C_59]: (k1_funct_1('#skF_6'(A_54), C_59)=np__1 | ~r2_hidden(C_59, A_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/1.98  tff(c_411, plain, (![A_120, C_121]: (k1_funct_1(A_120, '#skF_4'(A_120, k2_relat_1(A_120), C_121))=C_121 | ~r2_hidden(C_121, k2_relat_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.28/1.98  tff(c_436, plain, (![C_121, A_54]: (np__1=C_121 | ~r2_hidden(C_121, k2_relat_1('#skF_6'(A_54))) | ~v1_funct_1('#skF_6'(A_54)) | ~v1_relat_1('#skF_6'(A_54)) | ~r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_121), A_54))), inference(superposition, [status(thm), theory('equality')], [c_46, c_411])).
% 5.28/1.98  tff(c_2262, plain, (![C_210, A_211]: (np__1=C_210 | ~r2_hidden(C_210, k2_relat_1('#skF_6'(A_211))) | ~r2_hidden('#skF_4'('#skF_6'(A_211), k2_relat_1('#skF_6'(A_211)), C_210), A_211))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_436])).
% 5.28/1.98  tff(c_2313, plain, (![C_213, A_214]: (np__1=C_213 | ~r2_hidden(C_213, k2_relat_1('#skF_6'(A_214))))), inference(resolution, [status(thm)], [c_513, c_2262])).
% 5.28/1.98  tff(c_2385, plain, (![B_96, A_54]: (np__1=B_96 | A_54!='#skF_7')), inference(resolution, [status(thm)], [c_1406, c_2313])).
% 5.28/1.98  tff(c_2400, plain, (![A_54]: (A_54!='#skF_7')), inference(splitLeft, [status(thm)], [c_2385])).
% 5.28/1.98  tff(c_2405, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_2400])).
% 5.28/1.98  tff(c_2408, plain, (np__1='#skF_7'), inference(splitRight, [status(thm)], [c_2385])).
% 5.28/1.98  tff(c_2406, plain, (![B_96]: (np__1=B_96)), inference(splitRight, [status(thm)], [c_2385])).
% 5.28/1.98  tff(c_2736, plain, (![B_1526]: (B_1526='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2408, c_2406])).
% 5.28/1.98  tff(c_1408, plain, (![B_171, A_172]: (r2_hidden(B_171, k2_relat_1('#skF_6'(A_172))) | A_172!='#skF_7')), inference(splitLeft, [status(thm)], [c_1204])).
% 5.28/1.98  tff(c_527, plain, (![A_140, C_141]: (r2_hidden('#skF_4'('#skF_6'(A_140), k2_relat_1('#skF_6'(A_140)), C_141), A_140) | ~r2_hidden(C_141, k2_relat_1('#skF_6'(A_140))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_497])).
% 5.28/1.98  tff(c_196, plain, (![A_54, C_59]: (r2_hidden(np__1, k2_relat_1('#skF_6'(A_54))) | ~r2_hidden(C_59, k1_relat_1('#skF_6'(A_54))) | ~v1_funct_1('#skF_6'(A_54)) | ~v1_relat_1('#skF_6'(A_54)) | ~r2_hidden(C_59, A_54))), inference(superposition, [status(thm), theory('equality')], [c_46, c_190])).
% 5.28/1.98  tff(c_203, plain, (![A_54, C_59]: (r2_hidden(np__1, k2_relat_1('#skF_6'(A_54))) | ~r2_hidden(C_59, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_196])).
% 5.28/1.98  tff(c_657, plain, (![A_145, C_146]: (r2_hidden(np__1, k2_relat_1('#skF_6'(A_145))) | ~r2_hidden(C_146, k2_relat_1('#skF_6'(A_145))))), inference(resolution, [status(thm)], [c_527, c_203])).
% 5.28/1.98  tff(c_670, plain, (![A_145, C_136]: (r2_hidden(np__1, k2_relat_1('#skF_6'(A_145))) | ~r2_hidden(C_136, k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(A_145))))))), inference(resolution, [status(thm)], [c_513, c_657])).
% 5.28/1.98  tff(c_1487, plain, (![A_175]: (r2_hidden(np__1, k2_relat_1('#skF_6'(A_175))) | k2_relat_1('#skF_6'(A_175))!='#skF_7')), inference(resolution, [status(thm)], [c_1408, c_670])).
% 5.28/1.98  tff(c_216, plain, (![A_104, A_105, B_106]: ('#skF_6'(A_104)='#skF_5'(A_105, B_106) | A_105!='#skF_7' | A_104!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_180])).
% 5.28/1.98  tff(c_225, plain, (![A_104, D_53, B_106, A_105]: (k1_funct_1('#skF_6'(A_104), D_53)=B_106 | ~r2_hidden(D_53, A_105) | A_105!='#skF_7' | A_104!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_216, c_38])).
% 5.28/1.98  tff(c_1533, plain, (![A_104, B_106, A_175]: (k1_funct_1('#skF_6'(A_104), np__1)=B_106 | A_104!='#skF_7' | k2_relat_1('#skF_6'(A_175))!='#skF_7')), inference(resolution, [status(thm)], [c_1487, c_225])).
% 5.28/1.98  tff(c_2261, plain, (![A_175]: (k2_relat_1('#skF_6'(A_175))!='#skF_7')), inference(splitLeft, [status(thm)], [c_1533])).
% 5.28/1.98  tff(c_3031, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2736, c_2261])).
% 5.28/1.98  tff(c_3059, plain, (![A_2841]: (k1_funct_1('#skF_6'(A_2841), np__1)=k1_xboole_0 | A_2841!='#skF_7')), inference(splitRight, [status(thm)], [c_1533])).
% 5.28/1.98  tff(c_3032, plain, (![A_104, B_106]: (k1_funct_1('#skF_6'(A_104), np__1)=B_106 | A_104!='#skF_7')), inference(splitRight, [status(thm)], [c_1533])).
% 5.28/1.98  tff(c_3062, plain, (![B_106, A_2841]: (k1_xboole_0=B_106 | A_2841!='#skF_7' | A_2841!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3059, c_3032])).
% 5.28/1.98  tff(c_3681, plain, (![A_2841]: (A_2841!='#skF_7' | A_2841!='#skF_7')), inference(splitLeft, [status(thm)], [c_3062])).
% 5.28/1.98  tff(c_3735, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3681])).
% 5.28/1.98  tff(c_3738, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3062])).
% 5.28/1.98  tff(c_3736, plain, (![B_106]: (k1_xboole_0=B_106)), inference(splitRight, [status(thm)], [c_3062])).
% 5.28/1.98  tff(c_3961, plain, (![B_5222]: (B_5222='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3738, c_3736])).
% 5.28/1.98  tff(c_54, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.28/1.98  tff(c_4177, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3961, c_54])).
% 5.28/1.98  tff(c_4180, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1204])).
% 5.28/1.98  tff(c_4198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4180, c_54])).
% 5.28/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.98  
% 5.28/1.98  Inference rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Ref     : 3
% 5.28/1.98  #Sup     : 1343
% 5.28/1.98  #Fact    : 0
% 5.28/1.98  #Define  : 0
% 5.28/1.98  #Split   : 9
% 5.28/1.98  #Chain   : 0
% 5.28/1.98  #Close   : 0
% 5.28/1.98  
% 5.28/1.98  Ordering : KBO
% 5.28/1.98  
% 5.28/1.98  Simplification rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Subsume      : 372
% 5.28/1.98  #Demod        : 285
% 5.28/1.98  #Tautology    : 72
% 5.28/1.98  #SimpNegUnit  : 45
% 5.28/1.98  #BackRed      : 23
% 5.28/1.98  
% 5.28/1.98  #Partial instantiations: 1190
% 5.28/1.98  #Strategies tried      : 1
% 5.28/1.98  
% 5.28/1.98  Timing (in seconds)
% 5.28/1.98  ----------------------
% 5.51/1.98  Preprocessing        : 0.30
% 5.51/1.98  Parsing              : 0.15
% 5.51/1.98  CNF conversion       : 0.02
% 5.51/1.98  Main loop            : 0.91
% 5.51/1.98  Inferencing          : 0.32
% 5.51/1.98  Reduction            : 0.30
% 5.51/1.98  Demodulation         : 0.21
% 5.51/1.98  BG Simplification    : 0.04
% 5.51/1.98  Subsumption          : 0.19
% 5.51/1.98  Abstraction          : 0.05
% 5.51/1.98  MUC search           : 0.00
% 5.51/1.98  Cooper               : 0.00
% 5.51/1.98  Total                : 1.25
% 5.51/1.98  Index Insertion      : 0.00
% 5.51/1.98  Index Deletion       : 0.00
% 5.51/1.98  Index Matching       : 0.00
% 5.51/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
