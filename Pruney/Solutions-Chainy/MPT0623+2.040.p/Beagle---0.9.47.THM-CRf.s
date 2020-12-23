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
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 353 expanded)
%              Number of leaves         :   38 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  219 ( 876 expanded)
%              Number of equality atoms :  110 ( 483 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_101,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_397,plain,(
    ! [D_91,A_92,B_93] :
      ( r2_hidden(D_91,A_92)
      | ~ r2_hidden(D_91,k4_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_966,plain,(
    ! [A_164,B_165,B_166] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_164,B_165),B_166),A_164)
      | r1_tarski(k4_xboole_0(A_164,B_165),B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_407,plain,(
    ! [D_94,B_95,A_96] :
      ( ~ r2_hidden(D_94,B_95)
      | ~ r2_hidden(D_94,k4_xboole_0(A_96,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_415,plain,(
    ! [A_96,B_95,B_2] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_96,B_95),B_2),B_95)
      | r1_tarski(k4_xboole_0(A_96,B_95),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_407])).

tff(c_999,plain,(
    ! [A_164,B_166] : r1_tarski(k4_xboole_0(A_164,A_164),B_166) ),
    inference(resolution,[status(thm)],[c_966,c_415])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1216,plain,(
    ! [A_182,B_183,C_184] :
      ( r2_hidden('#skF_2'(A_182,B_183,C_184),A_182)
      | r2_hidden('#skF_3'(A_182,B_183,C_184),C_184)
      | k4_xboole_0(A_182,B_183) = C_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_248,plain,(
    ! [A_63,B_64] : ~ r2_hidden(A_63,k2_zfmisc_1(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_251,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_248])).

tff(c_1241,plain,(
    ! [B_183,C_184] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_183,C_184),C_184)
      | k4_xboole_0(k1_xboole_0,B_183) = C_184 ) ),
    inference(resolution,[status(thm)],[c_1216,c_251])).

tff(c_1274,plain,(
    ! [B_185,C_186] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_185,C_186),C_186)
      | k1_xboole_0 = C_186 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1241])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1356,plain,(
    ! [B_193,C_194,B_195] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_193,C_194),B_195)
      | ~ r1_tarski(C_194,B_195)
      | k1_xboole_0 = C_194 ) ),
    inference(resolution,[status(thm)],[c_1274,c_2])).

tff(c_1392,plain,(
    ! [C_196] :
      ( ~ r1_tarski(C_196,k1_xboole_0)
      | k1_xboole_0 = C_196 ) ),
    inference(resolution,[status(thm)],[c_1356,c_251])).

tff(c_1415,plain,(
    ! [A_164] : k4_xboole_0(A_164,A_164) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_999,c_1392])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1501,plain,(
    ! [A_204,B_205,C_206] :
      ( ~ r2_hidden('#skF_2'(A_204,B_205,C_206),B_205)
      | r2_hidden('#skF_3'(A_204,B_205,C_206),C_206)
      | k4_xboole_0(A_204,B_205) = C_206 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1504,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_1501])).

tff(c_1509,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k1_xboole_0 = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_1504])).

tff(c_72,plain,(
    ! [A_31,B_35] :
      ( k1_relat_1('#skF_7'(A_31,B_35)) = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    ! [A_31,B_35] :
      ( v1_funct_1('#skF_7'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    ! [A_31,B_35] :
      ( v1_relat_1('#skF_7'(A_31,B_35))
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_354,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_463,plain,(
    ! [A_107,B_108] :
      ( '#skF_1'(k1_tarski(A_107),B_108) = A_107
      | r1_tarski(k1_tarski(A_107),B_108) ) ),
    inference(resolution,[status(thm)],[c_354,c_30])).

tff(c_373,plain,(
    ! [A_85,B_86] :
      ( k2_relat_1('#skF_7'(A_85,B_86)) = k1_tarski(B_86)
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_38] :
      ( ~ r1_tarski(k2_relat_1(C_38),'#skF_8')
      | k1_relat_1(C_38) != '#skF_9'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_379,plain,(
    ! [B_86,A_85] :
      ( ~ r1_tarski(k1_tarski(B_86),'#skF_8')
      | k1_relat_1('#skF_7'(A_85,B_86)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_85,B_86))
      | ~ v1_relat_1('#skF_7'(A_85,B_86))
      | k1_xboole_0 = A_85 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_78])).

tff(c_502,plain,(
    ! [A_113,A_114] :
      ( k1_relat_1('#skF_7'(A_113,A_114)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_113,A_114))
      | ~ v1_relat_1('#skF_7'(A_113,A_114))
      | k1_xboole_0 = A_113
      | '#skF_1'(k1_tarski(A_114),'#skF_8') = A_114 ) ),
    inference(resolution,[status(thm)],[c_463,c_379])).

tff(c_824,plain,(
    ! [A_145,B_146] :
      ( k1_relat_1('#skF_7'(A_145,B_146)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_145,B_146))
      | '#skF_1'(k1_tarski(B_146),'#skF_8') = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_76,c_502])).

tff(c_1061,plain,(
    ! [A_174,B_175] :
      ( k1_relat_1('#skF_7'(A_174,B_175)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_175),'#skF_8') = B_175
      | k1_xboole_0 = A_174 ) ),
    inference(resolution,[status(thm)],[c_74,c_824])).

tff(c_1064,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_9'
      | '#skF_1'(k1_tarski(B_35),'#skF_8') = B_35
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1061])).

tff(c_1066,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_60,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_50])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [C_43] :
      ( ~ r1_tarski(k2_relat_1(C_43),'#skF_8')
      | k1_relat_1(C_43) != '#skF_9'
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_103,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_100])).

tff(c_105,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_54,c_26,c_103])).

tff(c_145,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_64,plain,(
    ! [A_25] : k1_relat_1('#skF_6'(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_68,plain,(
    ! [A_25] : v1_relat_1('#skF_6'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_192,plain,(
    ! [A_61] :
      ( k1_relat_1(A_61) != k1_xboole_0
      | k1_xboole_0 = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_204,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_6'(A_25)) != k1_xboole_0
      | '#skF_6'(A_25) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_192])).

tff(c_214,plain,(
    ! [A_62] :
      ( k1_xboole_0 != A_62
      | '#skF_6'(A_62) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_204])).

tff(c_66,plain,(
    ! [A_25] : v1_funct_1('#skF_6'(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_222,plain,(
    ! [A_62] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_66])).

tff(c_230,plain,(
    ! [A_62] : k1_xboole_0 != A_62 ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_222])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_28])).

tff(c_246,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_246])).

tff(c_1109,plain,(
    ! [B_176] : '#skF_1'(k1_tarski(B_176),'#skF_8') = B_176 ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1143,plain,(
    ! [B_177] :
      ( ~ r2_hidden(B_177,'#skF_8')
      | r1_tarski(k1_tarski(B_177),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1109,c_4])).

tff(c_1351,plain,(
    ! [A_191,B_192] :
      ( k1_relat_1('#skF_7'(A_191,B_192)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_191,B_192))
      | ~ v1_relat_1('#skF_7'(A_191,B_192))
      | k1_xboole_0 = A_191
      | ~ r2_hidden(B_192,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1143,c_379])).

tff(c_1631,plain,(
    ! [A_214,B_215] :
      ( k1_relat_1('#skF_7'(A_214,B_215)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_214,B_215))
      | ~ r2_hidden(B_215,'#skF_8')
      | k1_xboole_0 = A_214 ) ),
    inference(resolution,[status(thm)],[c_76,c_1351])).

tff(c_1658,plain,(
    ! [A_219,B_220] :
      ( k1_relat_1('#skF_7'(A_219,B_220)) != '#skF_9'
      | ~ r2_hidden(B_220,'#skF_8')
      | k1_xboole_0 = A_219 ) ),
    inference(resolution,[status(thm)],[c_74,c_1631])).

tff(c_1661,plain,(
    ! [A_31,B_35] :
      ( A_31 != '#skF_9'
      | ~ r2_hidden(B_35,'#skF_8')
      | k1_xboole_0 = A_31
      | k1_xboole_0 = A_31 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1658])).

tff(c_1663,plain,(
    ! [B_221] : ~ r2_hidden(B_221,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1661])).

tff(c_1671,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1509,c_1663])).

tff(c_1714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1671])).

tff(c_1716,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1661])).

tff(c_1766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_246])).

tff(c_1768,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1767,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1778,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_1767])).

tff(c_1772,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_86])).

tff(c_1787,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1772])).

tff(c_1771,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1767,c_54])).

tff(c_1798,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1778,c_1771])).

tff(c_1770,plain,(
    ! [A_12] : r1_tarski('#skF_9',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_26])).

tff(c_1803,plain,(
    ! [A_12] : r1_tarski('#skF_8',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1770])).

tff(c_1769,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1767,c_52])).

tff(c_1805,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_1778,c_1769])).

tff(c_1788,plain,(
    ! [C_38] :
      ( ~ r1_tarski(k2_relat_1(C_38),'#skF_8')
      | k1_relat_1(C_38) != '#skF_8'
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_78])).

tff(c_1809,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_1788])).

tff(c_1813,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_1798,c_1803,c_1809])).

tff(c_58,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1887,plain,(
    ! [A_240] :
      ( k1_relat_1(A_240) != '#skF_8'
      | A_240 = '#skF_8'
      | ~ v1_relat_1(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_1768,c_58])).

tff(c_1899,plain,(
    ! [A_25] :
      ( k1_relat_1('#skF_6'(A_25)) != '#skF_8'
      | '#skF_6'(A_25) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_68,c_1887])).

tff(c_1909,plain,(
    ! [A_241] :
      ( A_241 != '#skF_8'
      | '#skF_6'(A_241) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1899])).

tff(c_1917,plain,(
    ! [A_241] :
      ( v1_funct_1('#skF_8')
      | A_241 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1909,c_66])).

tff(c_1925,plain,(
    ! [A_241] : A_241 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1813,c_1917])).

tff(c_46,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1841,plain,(
    ! [B_20] : k2_zfmisc_1('#skF_8',B_20) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_1768,c_46])).

tff(c_1941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1925,c_1841])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.75  
% 3.66/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.75  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 3.66/1.75  
% 3.66/1.75  %Foreground sorts:
% 3.66/1.75  
% 3.66/1.75  
% 3.66/1.75  %Background operators:
% 3.66/1.75  
% 3.66/1.75  
% 3.66/1.75  %Foreground operators:
% 3.66/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.66/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.66/1.75  tff('#skF_9', type, '#skF_9': $i).
% 3.66/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.75  tff('#skF_8', type, '#skF_8': $i).
% 3.66/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.66/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.66/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.75  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.66/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.66/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.75  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.66/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.66/1.75  
% 3.66/1.77  tff(f_119, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.66/1.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.77  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.66/1.77  tff(f_46, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.66/1.77  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.66/1.77  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.66/1.77  tff(f_101, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.66/1.77  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.66/1.77  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.66/1.77  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.66/1.77  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.66/1.77  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.66/1.77  tff(f_88, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.66/1.77  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.66/1.77  tff(c_80, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.66/1.77  tff(c_99, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_80])).
% 3.66/1.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.77  tff(c_397, plain, (![D_91, A_92, B_93]: (r2_hidden(D_91, A_92) | ~r2_hidden(D_91, k4_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.77  tff(c_966, plain, (![A_164, B_165, B_166]: (r2_hidden('#skF_1'(k4_xboole_0(A_164, B_165), B_166), A_164) | r1_tarski(k4_xboole_0(A_164, B_165), B_166))), inference(resolution, [status(thm)], [c_6, c_397])).
% 3.66/1.77  tff(c_407, plain, (![D_94, B_95, A_96]: (~r2_hidden(D_94, B_95) | ~r2_hidden(D_94, k4_xboole_0(A_96, B_95)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.77  tff(c_415, plain, (![A_96, B_95, B_2]: (~r2_hidden('#skF_1'(k4_xboole_0(A_96, B_95), B_2), B_95) | r1_tarski(k4_xboole_0(A_96, B_95), B_2))), inference(resolution, [status(thm)], [c_6, c_407])).
% 3.66/1.77  tff(c_999, plain, (![A_164, B_166]: (r1_tarski(k4_xboole_0(A_164, A_164), B_166))), inference(resolution, [status(thm)], [c_966, c_415])).
% 3.66/1.77  tff(c_28, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.77  tff(c_1216, plain, (![A_182, B_183, C_184]: (r2_hidden('#skF_2'(A_182, B_183, C_184), A_182) | r2_hidden('#skF_3'(A_182, B_183, C_184), C_184) | k4_xboole_0(A_182, B_183)=C_184)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.77  tff(c_44, plain, (![A_19]: (k2_zfmisc_1(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.77  tff(c_248, plain, (![A_63, B_64]: (~r2_hidden(A_63, k2_zfmisc_1(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.77  tff(c_251, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_248])).
% 3.66/1.77  tff(c_1241, plain, (![B_183, C_184]: (r2_hidden('#skF_3'(k1_xboole_0, B_183, C_184), C_184) | k4_xboole_0(k1_xboole_0, B_183)=C_184)), inference(resolution, [status(thm)], [c_1216, c_251])).
% 3.66/1.77  tff(c_1274, plain, (![B_185, C_186]: (r2_hidden('#skF_3'(k1_xboole_0, B_185, C_186), C_186) | k1_xboole_0=C_186)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1241])).
% 3.66/1.77  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.77  tff(c_1356, plain, (![B_193, C_194, B_195]: (r2_hidden('#skF_3'(k1_xboole_0, B_193, C_194), B_195) | ~r1_tarski(C_194, B_195) | k1_xboole_0=C_194)), inference(resolution, [status(thm)], [c_1274, c_2])).
% 3.66/1.77  tff(c_1392, plain, (![C_196]: (~r1_tarski(C_196, k1_xboole_0) | k1_xboole_0=C_196)), inference(resolution, [status(thm)], [c_1356, c_251])).
% 3.66/1.77  tff(c_1415, plain, (![A_164]: (k4_xboole_0(A_164, A_164)=k1_xboole_0)), inference(resolution, [status(thm)], [c_999, c_1392])).
% 3.66/1.77  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.77  tff(c_1501, plain, (![A_204, B_205, C_206]: (~r2_hidden('#skF_2'(A_204, B_205, C_206), B_205) | r2_hidden('#skF_3'(A_204, B_205, C_206), C_206) | k4_xboole_0(A_204, B_205)=C_206)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.77  tff(c_1504, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_1501])).
% 3.66/1.77  tff(c_1509, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k1_xboole_0=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_1504])).
% 3.66/1.77  tff(c_72, plain, (![A_31, B_35]: (k1_relat_1('#skF_7'(A_31, B_35))=A_31 | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.77  tff(c_74, plain, (![A_31, B_35]: (v1_funct_1('#skF_7'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.77  tff(c_76, plain, (![A_31, B_35]: (v1_relat_1('#skF_7'(A_31, B_35)) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.77  tff(c_354, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.77  tff(c_30, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.77  tff(c_463, plain, (![A_107, B_108]: ('#skF_1'(k1_tarski(A_107), B_108)=A_107 | r1_tarski(k1_tarski(A_107), B_108))), inference(resolution, [status(thm)], [c_354, c_30])).
% 3.66/1.77  tff(c_373, plain, (![A_85, B_86]: (k2_relat_1('#skF_7'(A_85, B_86))=k1_tarski(B_86) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.77  tff(c_78, plain, (![C_38]: (~r1_tarski(k2_relat_1(C_38), '#skF_8') | k1_relat_1(C_38)!='#skF_9' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.66/1.77  tff(c_379, plain, (![B_86, A_85]: (~r1_tarski(k1_tarski(B_86), '#skF_8') | k1_relat_1('#skF_7'(A_85, B_86))!='#skF_9' | ~v1_funct_1('#skF_7'(A_85, B_86)) | ~v1_relat_1('#skF_7'(A_85, B_86)) | k1_xboole_0=A_85)), inference(superposition, [status(thm), theory('equality')], [c_373, c_78])).
% 3.66/1.77  tff(c_502, plain, (![A_113, A_114]: (k1_relat_1('#skF_7'(A_113, A_114))!='#skF_9' | ~v1_funct_1('#skF_7'(A_113, A_114)) | ~v1_relat_1('#skF_7'(A_113, A_114)) | k1_xboole_0=A_113 | '#skF_1'(k1_tarski(A_114), '#skF_8')=A_114)), inference(resolution, [status(thm)], [c_463, c_379])).
% 3.66/1.77  tff(c_824, plain, (![A_145, B_146]: (k1_relat_1('#skF_7'(A_145, B_146))!='#skF_9' | ~v1_funct_1('#skF_7'(A_145, B_146)) | '#skF_1'(k1_tarski(B_146), '#skF_8')=B_146 | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_76, c_502])).
% 4.00/1.77  tff(c_1061, plain, (![A_174, B_175]: (k1_relat_1('#skF_7'(A_174, B_175))!='#skF_9' | '#skF_1'(k1_tarski(B_175), '#skF_8')=B_175 | k1_xboole_0=A_174)), inference(resolution, [status(thm)], [c_74, c_824])).
% 4.00/1.77  tff(c_1064, plain, (![A_31, B_35]: (A_31!='#skF_9' | '#skF_1'(k1_tarski(B_35), '#skF_8')=B_35 | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_72, c_1061])).
% 4.00/1.77  tff(c_1066, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1064])).
% 4.00/1.77  tff(c_60, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.00/1.77  tff(c_50, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.00/1.77  tff(c_86, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_50])).
% 4.00/1.77  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.00/1.77  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.00/1.77  tff(c_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.00/1.77  tff(c_100, plain, (![C_43]: (~r1_tarski(k2_relat_1(C_43), '#skF_8') | k1_relat_1(C_43)!='#skF_9' | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.00/1.77  tff(c_103, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_100])).
% 4.00/1.77  tff(c_105, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_54, c_26, c_103])).
% 4.00/1.77  tff(c_145, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_105])).
% 4.00/1.77  tff(c_64, plain, (![A_25]: (k1_relat_1('#skF_6'(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.00/1.77  tff(c_68, plain, (![A_25]: (v1_relat_1('#skF_6'(A_25)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.00/1.77  tff(c_192, plain, (![A_61]: (k1_relat_1(A_61)!=k1_xboole_0 | k1_xboole_0=A_61 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.00/1.77  tff(c_204, plain, (![A_25]: (k1_relat_1('#skF_6'(A_25))!=k1_xboole_0 | '#skF_6'(A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_192])).
% 4.00/1.77  tff(c_214, plain, (![A_62]: (k1_xboole_0!=A_62 | '#skF_6'(A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_204])).
% 4.00/1.77  tff(c_66, plain, (![A_25]: (v1_funct_1('#skF_6'(A_25)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.00/1.77  tff(c_222, plain, (![A_62]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_62)), inference(superposition, [status(thm), theory('equality')], [c_214, c_66])).
% 4.00/1.77  tff(c_230, plain, (![A_62]: (k1_xboole_0!=A_62)), inference(negUnitSimplification, [status(thm)], [c_145, c_222])).
% 4.00/1.77  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_28])).
% 4.00/1.77  tff(c_246, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_105])).
% 4.00/1.77  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1066, c_246])).
% 4.00/1.77  tff(c_1109, plain, (![B_176]: ('#skF_1'(k1_tarski(B_176), '#skF_8')=B_176)), inference(splitRight, [status(thm)], [c_1064])).
% 4.00/1.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.00/1.77  tff(c_1143, plain, (![B_177]: (~r2_hidden(B_177, '#skF_8') | r1_tarski(k1_tarski(B_177), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1109, c_4])).
% 4.00/1.77  tff(c_1351, plain, (![A_191, B_192]: (k1_relat_1('#skF_7'(A_191, B_192))!='#skF_9' | ~v1_funct_1('#skF_7'(A_191, B_192)) | ~v1_relat_1('#skF_7'(A_191, B_192)) | k1_xboole_0=A_191 | ~r2_hidden(B_192, '#skF_8'))), inference(resolution, [status(thm)], [c_1143, c_379])).
% 4.00/1.77  tff(c_1631, plain, (![A_214, B_215]: (k1_relat_1('#skF_7'(A_214, B_215))!='#skF_9' | ~v1_funct_1('#skF_7'(A_214, B_215)) | ~r2_hidden(B_215, '#skF_8') | k1_xboole_0=A_214)), inference(resolution, [status(thm)], [c_76, c_1351])).
% 4.00/1.77  tff(c_1658, plain, (![A_219, B_220]: (k1_relat_1('#skF_7'(A_219, B_220))!='#skF_9' | ~r2_hidden(B_220, '#skF_8') | k1_xboole_0=A_219)), inference(resolution, [status(thm)], [c_74, c_1631])).
% 4.00/1.77  tff(c_1661, plain, (![A_31, B_35]: (A_31!='#skF_9' | ~r2_hidden(B_35, '#skF_8') | k1_xboole_0=A_31 | k1_xboole_0=A_31)), inference(superposition, [status(thm), theory('equality')], [c_72, c_1658])).
% 4.00/1.77  tff(c_1663, plain, (![B_221]: (~r2_hidden(B_221, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1661])).
% 4.00/1.77  tff(c_1671, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1509, c_1663])).
% 4.00/1.77  tff(c_1714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1671])).
% 4.00/1.77  tff(c_1716, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1661])).
% 4.00/1.77  tff(c_1766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1716, c_246])).
% 4.00/1.77  tff(c_1768, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 4.00/1.77  tff(c_1767, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_80])).
% 4.00/1.77  tff(c_1778, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_1767])).
% 4.00/1.77  tff(c_1772, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_86])).
% 4.00/1.77  tff(c_1787, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1772])).
% 4.00/1.77  tff(c_1771, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1767, c_54])).
% 4.00/1.77  tff(c_1798, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1778, c_1771])).
% 4.00/1.77  tff(c_1770, plain, (![A_12]: (r1_tarski('#skF_9', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_26])).
% 4.00/1.77  tff(c_1803, plain, (![A_12]: (r1_tarski('#skF_8', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1770])).
% 4.00/1.77  tff(c_1769, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1767, c_52])).
% 4.00/1.77  tff(c_1805, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_1778, c_1769])).
% 4.00/1.77  tff(c_1788, plain, (![C_38]: (~r1_tarski(k2_relat_1(C_38), '#skF_8') | k1_relat_1(C_38)!='#skF_8' | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(demodulation, [status(thm), theory('equality')], [c_1778, c_78])).
% 4.00/1.77  tff(c_1809, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1805, c_1788])).
% 4.00/1.77  tff(c_1813, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_1798, c_1803, c_1809])).
% 4.00/1.77  tff(c_58, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.00/1.77  tff(c_1887, plain, (![A_240]: (k1_relat_1(A_240)!='#skF_8' | A_240='#skF_8' | ~v1_relat_1(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_1768, c_58])).
% 4.00/1.77  tff(c_1899, plain, (![A_25]: (k1_relat_1('#skF_6'(A_25))!='#skF_8' | '#skF_6'(A_25)='#skF_8')), inference(resolution, [status(thm)], [c_68, c_1887])).
% 4.00/1.77  tff(c_1909, plain, (![A_241]: (A_241!='#skF_8' | '#skF_6'(A_241)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1899])).
% 4.00/1.77  tff(c_1917, plain, (![A_241]: (v1_funct_1('#skF_8') | A_241!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1909, c_66])).
% 4.00/1.77  tff(c_1925, plain, (![A_241]: (A_241!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1813, c_1917])).
% 4.00/1.77  tff(c_46, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.00/1.77  tff(c_1841, plain, (![B_20]: (k2_zfmisc_1('#skF_8', B_20)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_1768, c_46])).
% 4.00/1.77  tff(c_1941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1925, c_1841])).
% 4.00/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.77  
% 4.00/1.77  Inference rules
% 4.00/1.77  ----------------------
% 4.00/1.77  #Ref     : 0
% 4.00/1.77  #Sup     : 383
% 4.00/1.77  #Fact    : 0
% 4.00/1.77  #Define  : 0
% 4.00/1.77  #Split   : 4
% 4.00/1.77  #Chain   : 0
% 4.00/1.77  #Close   : 0
% 4.00/1.77  
% 4.00/1.77  Ordering : KBO
% 4.00/1.77  
% 4.00/1.77  Simplification rules
% 4.00/1.77  ----------------------
% 4.00/1.77  #Subsume      : 59
% 4.00/1.77  #Demod        : 280
% 4.00/1.77  #Tautology    : 193
% 4.00/1.77  #SimpNegUnit  : 42
% 4.00/1.77  #BackRed      : 112
% 4.00/1.77  
% 4.00/1.77  #Partial instantiations: 0
% 4.00/1.77  #Strategies tried      : 1
% 4.00/1.77  
% 4.00/1.77  Timing (in seconds)
% 4.00/1.77  ----------------------
% 4.00/1.78  Preprocessing        : 0.34
% 4.00/1.78  Parsing              : 0.18
% 4.00/1.78  CNF conversion       : 0.03
% 4.00/1.78  Main loop            : 0.59
% 4.00/1.78  Inferencing          : 0.22
% 4.00/1.78  Reduction            : 0.17
% 4.00/1.78  Demodulation         : 0.12
% 4.00/1.78  BG Simplification    : 0.03
% 4.00/1.78  Subsumption          : 0.11
% 4.00/1.78  Abstraction          : 0.03
% 4.00/1.78  MUC search           : 0.00
% 4.00/1.78  Cooper               : 0.00
% 4.00/1.78  Total                : 0.98
% 4.00/1.78  Index Insertion      : 0.00
% 4.00/1.78  Index Deletion       : 0.00
% 4.00/1.78  Index Matching       : 0.00
% 4.00/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
