%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 531 expanded)
%              Number of leaves         :   39 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  225 (1336 expanded)
%              Number of equality atoms :  131 ( 785 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

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

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
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

tff(f_76,axiom,(
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

tff(c_116,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_30,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_281,plain,(
    ! [A_70,B_71] : k1_setfam_1(k2_tarski(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_368,plain,(
    ! [B_80,A_81] : k1_setfam_1(k2_tarski(B_80,A_81)) = k3_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_281])).

tff(c_52,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_391,plain,(
    ! [B_82,A_83] : k3_xboole_0(B_82,A_83) = k3_xboole_0(A_83,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_52])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_413,plain,(
    ! [A_83] : k3_xboole_0(k1_xboole_0,A_83) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_26])).

tff(c_1932,plain,(
    ! [A_216,B_217,C_218] :
      ( r2_hidden('#skF_2'(A_216,B_217,C_218),A_216)
      | r2_hidden('#skF_3'(A_216,B_217,C_218),C_218)
      | k3_xboole_0(A_216,B_217) = C_218 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_21] : ~ r2_hidden(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_132])).

tff(c_1957,plain,(
    ! [B_217,C_218] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_217,C_218),C_218)
      | k3_xboole_0(k1_xboole_0,B_217) = C_218 ) ),
    inference(resolution,[status(thm)],[c_1932,c_138])).

tff(c_1987,plain,(
    ! [B_217,C_218] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_217,C_218),C_218)
      | k1_xboole_0 = C_218 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_1957])).

tff(c_72,plain,(
    ! [A_34,B_38] :
      ( k1_relat_1('#skF_7'(A_34,B_38)) = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    ! [A_34,B_38] :
      ( v1_funct_1('#skF_7'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    ! [A_34,B_38] :
      ( v1_relat_1('#skF_7'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_481,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_567,plain,(
    ! [A_104,B_105] :
      ( '#skF_1'(k1_tarski(A_104),B_105) = A_104
      | r1_tarski(k1_tarski(A_104),B_105) ) ),
    inference(resolution,[status(thm)],[c_481,c_32])).

tff(c_540,plain,(
    ! [A_95,B_96] :
      ( k2_relat_1('#skF_7'(A_95,B_96)) = k1_tarski(B_96)
      | k1_xboole_0 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [C_41] :
      ( ~ r1_tarski(k2_relat_1(C_41),'#skF_8')
      | k1_relat_1(C_41) != '#skF_9'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_546,plain,(
    ! [B_96,A_95] :
      ( ~ r1_tarski(k1_tarski(B_96),'#skF_8')
      | k1_relat_1('#skF_7'(A_95,B_96)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_95,B_96))
      | ~ v1_relat_1('#skF_7'(A_95,B_96))
      | k1_xboole_0 = A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_78])).

tff(c_716,plain,(
    ! [A_123,A_124] :
      ( k1_relat_1('#skF_7'(A_123,A_124)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_123,A_124))
      | ~ v1_relat_1('#skF_7'(A_123,A_124))
      | k1_xboole_0 = A_123
      | '#skF_1'(k1_tarski(A_124),'#skF_8') = A_124 ) ),
    inference(resolution,[status(thm)],[c_567,c_546])).

tff(c_1068,plain,(
    ! [A_154,B_155] :
      ( k1_relat_1('#skF_7'(A_154,B_155)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_154,B_155))
      | '#skF_1'(k1_tarski(B_155),'#skF_8') = B_155
      | k1_xboole_0 = A_154 ) ),
    inference(resolution,[status(thm)],[c_76,c_716])).

tff(c_1469,plain,(
    ! [A_184,B_185] :
      ( k1_relat_1('#skF_7'(A_184,B_185)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_185),'#skF_8') = B_185
      | k1_xboole_0 = A_184 ) ),
    inference(resolution,[status(thm)],[c_74,c_1068])).

tff(c_1472,plain,(
    ! [A_34,B_38] :
      ( A_34 != '#skF_9'
      | '#skF_1'(k1_tarski(B_38),'#skF_8') = B_38
      | k1_xboole_0 = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1469])).

tff(c_1643,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_181,plain,(
    ! [C_61] :
      ( ~ r1_tarski(k2_relat_1(C_61),'#skF_8')
      | k1_relat_1(C_61) != '#skF_9'
      | ~ v1_funct_1(C_61)
      | ~ v1_relat_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_184,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_181])).

tff(c_186,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_28,c_184])).

tff(c_187,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_64,plain,(
    ! [A_28] : k1_relat_1('#skF_6'(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_68,plain,(
    ! [A_28] : v1_relat_1('#skF_6'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_203,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_209,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_6'(A_28)) != k1_xboole_0
      | '#skF_6'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_203])).

tff(c_214,plain,(
    ! [A_65] :
      ( k1_xboole_0 != A_65
      | '#skF_6'(A_65) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_209])).

tff(c_224,plain,(
    ! [A_65] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_68])).

tff(c_230,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_224])).

tff(c_48,plain,(
    ! [B_22] : k2_zfmisc_1(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_48])).

tff(c_252,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_254,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_1686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1643,c_254])).

tff(c_1689,plain,(
    ! [B_199] : '#skF_1'(k1_tarski(B_199),'#skF_8') = B_199 ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1723,plain,(
    ! [B_200] :
      ( ~ r2_hidden(B_200,'#skF_8')
      | r1_tarski(k1_tarski(B_200),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1689,c_4])).

tff(c_1731,plain,(
    ! [A_201,B_202] :
      ( k1_relat_1('#skF_7'(A_201,B_202)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_201,B_202))
      | ~ v1_relat_1('#skF_7'(A_201,B_202))
      | k1_xboole_0 = A_201
      | ~ r2_hidden(B_202,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1723,c_546])).

tff(c_2113,plain,(
    ! [A_225,B_226] :
      ( k1_relat_1('#skF_7'(A_225,B_226)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_225,B_226))
      | ~ r2_hidden(B_226,'#skF_8')
      | k1_xboole_0 = A_225 ) ),
    inference(resolution,[status(thm)],[c_76,c_1731])).

tff(c_2118,plain,(
    ! [A_227,B_228] :
      ( k1_relat_1('#skF_7'(A_227,B_228)) != '#skF_9'
      | ~ r2_hidden(B_228,'#skF_8')
      | k1_xboole_0 = A_227 ) ),
    inference(resolution,[status(thm)],[c_74,c_2113])).

tff(c_2121,plain,(
    ! [A_34,B_38] :
      ( A_34 != '#skF_9'
      | ~ r2_hidden(B_38,'#skF_8')
      | k1_xboole_0 = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2118])).

tff(c_2123,plain,(
    ! [B_229] : ~ r2_hidden(B_229,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2121])).

tff(c_2131,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1987,c_2123])).

tff(c_2204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_2131])).

tff(c_2206,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2121])).

tff(c_2254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2206,c_254])).

tff(c_2256,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_2255,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_2275,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2255])).

tff(c_2257,plain,(
    ! [A_230] :
      ( k1_relat_1(A_230) != k1_xboole_0
      | k1_xboole_0 = A_230
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2266,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_6'(A_28)) != k1_xboole_0
      | '#skF_6'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_2257])).

tff(c_2273,plain,(
    ! [A_28] :
      ( k1_xboole_0 != A_28
      | '#skF_6'(A_28) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2266])).

tff(c_2358,plain,(
    ! [A_238] :
      ( A_238 != '#skF_9'
      | '#skF_6'(A_238) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_2273])).

tff(c_66,plain,(
    ! [A_28] : v1_funct_1('#skF_6'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2366,plain,(
    ! [A_238] :
      ( v1_funct_1('#skF_9')
      | A_238 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_66])).

tff(c_2374,plain,(
    ! [A_238] : A_238 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_2275,c_2366])).

tff(c_2282,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2256,c_2256,c_46])).

tff(c_2384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2374,c_2282])).

tff(c_2386,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2385,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2396,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_2385])).

tff(c_2391,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_2385,c_56])).

tff(c_2412,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_2396,c_2391])).

tff(c_2390,plain,(
    ! [A_13] : r1_tarski('#skF_9',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_28])).

tff(c_2410,plain,(
    ! [A_13] : r1_tarski('#skF_8',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_2390])).

tff(c_2389,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_2385,c_54])).

tff(c_2405,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_2396,c_2389])).

tff(c_2450,plain,(
    ! [C_243] :
      ( ~ r1_tarski(k2_relat_1(C_243),'#skF_8')
      | k1_relat_1(C_243) != '#skF_8'
      | ~ v1_funct_1(C_243)
      | ~ v1_relat_1(C_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_78])).

tff(c_2453,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2405,c_2450])).

tff(c_2455,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2410,c_2453])).

tff(c_2456,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2455])).

tff(c_60,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2509,plain,(
    ! [A_255] :
      ( k1_relat_1(A_255) != '#skF_8'
      | A_255 = '#skF_8'
      | ~ v1_relat_1(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_2386,c_60])).

tff(c_2515,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_6'(A_28)) != '#skF_8'
      | '#skF_6'(A_28) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_68,c_2509])).

tff(c_2520,plain,(
    ! [A_256] :
      ( A_256 != '#skF_8'
      | '#skF_6'(A_256) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2515])).

tff(c_2530,plain,(
    ! [A_256] :
      ( v1_relat_1('#skF_8')
      | A_256 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2520,c_68])).

tff(c_2536,plain,(
    ! [A_256] : A_256 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2456,c_2530])).

tff(c_2388,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_2385,c_26])).

tff(c_2441,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_2396,c_2388])).

tff(c_2549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2536,c_2441])).

tff(c_2550,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2455])).

tff(c_2636,plain,(
    ! [A_271] :
      ( k1_relat_1(A_271) != '#skF_8'
      | A_271 = '#skF_8'
      | ~ v1_relat_1(A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_2386,c_60])).

tff(c_2645,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_6'(A_28)) != '#skF_8'
      | '#skF_6'(A_28) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_68,c_2636])).

tff(c_2654,plain,(
    ! [A_272] :
      ( A_272 != '#skF_8'
      | '#skF_6'(A_272) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2645])).

tff(c_2662,plain,(
    ! [A_272] :
      ( v1_funct_1('#skF_8')
      | A_272 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2654,c_66])).

tff(c_2670,plain,(
    ! [A_272] : A_272 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_2550,c_2662])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2670,c_2441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.72  
% 4.11/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.72  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 4.11/1.72  
% 4.11/1.72  %Foreground sorts:
% 4.11/1.72  
% 4.11/1.72  
% 4.11/1.72  %Background operators:
% 4.11/1.72  
% 4.11/1.72  
% 4.11/1.72  %Foreground operators:
% 4.11/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.11/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.11/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.11/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.11/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.11/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.11/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.11/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.11/1.72  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.11/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.72  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.11/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.11/1.72  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.11/1.72  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.11/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.11/1.72  
% 4.11/1.74  tff(f_119, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 4.11/1.74  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.11/1.74  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.11/1.74  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.11/1.74  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.11/1.74  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.11/1.74  tff(f_63, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.11/1.74  tff(f_101, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 4.11/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.11/1.74  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.11/1.74  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.11/1.74  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.11/1.74  tff(f_88, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 4.11/1.74  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.11/1.74  tff(c_80, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.11/1.74  tff(c_116, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_80])).
% 4.11/1.74  tff(c_30, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.11/1.74  tff(c_281, plain, (![A_70, B_71]: (k1_setfam_1(k2_tarski(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.11/1.74  tff(c_368, plain, (![B_80, A_81]: (k1_setfam_1(k2_tarski(B_80, A_81))=k3_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_30, c_281])).
% 4.11/1.74  tff(c_52, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.11/1.74  tff(c_391, plain, (![B_82, A_83]: (k3_xboole_0(B_82, A_83)=k3_xboole_0(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_368, c_52])).
% 4.11/1.74  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.11/1.74  tff(c_413, plain, (![A_83]: (k3_xboole_0(k1_xboole_0, A_83)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_391, c_26])).
% 4.11/1.74  tff(c_1932, plain, (![A_216, B_217, C_218]: (r2_hidden('#skF_2'(A_216, B_217, C_218), A_216) | r2_hidden('#skF_3'(A_216, B_217, C_218), C_218) | k3_xboole_0(A_216, B_217)=C_218)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.74  tff(c_46, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.11/1.74  tff(c_132, plain, (![A_50, B_51]: (~r2_hidden(A_50, k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.11/1.74  tff(c_138, plain, (![A_21]: (~r2_hidden(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_132])).
% 4.11/1.74  tff(c_1957, plain, (![B_217, C_218]: (r2_hidden('#skF_3'(k1_xboole_0, B_217, C_218), C_218) | k3_xboole_0(k1_xboole_0, B_217)=C_218)), inference(resolution, [status(thm)], [c_1932, c_138])).
% 4.11/1.74  tff(c_1987, plain, (![B_217, C_218]: (r2_hidden('#skF_3'(k1_xboole_0, B_217, C_218), C_218) | k1_xboole_0=C_218)), inference(demodulation, [status(thm), theory('equality')], [c_413, c_1957])).
% 4.11/1.74  tff(c_72, plain, (![A_34, B_38]: (k1_relat_1('#skF_7'(A_34, B_38))=A_34 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.11/1.74  tff(c_74, plain, (![A_34, B_38]: (v1_funct_1('#skF_7'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.11/1.74  tff(c_76, plain, (![A_34, B_38]: (v1_relat_1('#skF_7'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.11/1.74  tff(c_481, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.74  tff(c_32, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.74  tff(c_567, plain, (![A_104, B_105]: ('#skF_1'(k1_tarski(A_104), B_105)=A_104 | r1_tarski(k1_tarski(A_104), B_105))), inference(resolution, [status(thm)], [c_481, c_32])).
% 4.11/1.74  tff(c_540, plain, (![A_95, B_96]: (k2_relat_1('#skF_7'(A_95, B_96))=k1_tarski(B_96) | k1_xboole_0=A_95)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.11/1.74  tff(c_78, plain, (![C_41]: (~r1_tarski(k2_relat_1(C_41), '#skF_8') | k1_relat_1(C_41)!='#skF_9' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.11/1.74  tff(c_546, plain, (![B_96, A_95]: (~r1_tarski(k1_tarski(B_96), '#skF_8') | k1_relat_1('#skF_7'(A_95, B_96))!='#skF_9' | ~v1_funct_1('#skF_7'(A_95, B_96)) | ~v1_relat_1('#skF_7'(A_95, B_96)) | k1_xboole_0=A_95)), inference(superposition, [status(thm), theory('equality')], [c_540, c_78])).
% 4.11/1.74  tff(c_716, plain, (![A_123, A_124]: (k1_relat_1('#skF_7'(A_123, A_124))!='#skF_9' | ~v1_funct_1('#skF_7'(A_123, A_124)) | ~v1_relat_1('#skF_7'(A_123, A_124)) | k1_xboole_0=A_123 | '#skF_1'(k1_tarski(A_124), '#skF_8')=A_124)), inference(resolution, [status(thm)], [c_567, c_546])).
% 4.11/1.74  tff(c_1068, plain, (![A_154, B_155]: (k1_relat_1('#skF_7'(A_154, B_155))!='#skF_9' | ~v1_funct_1('#skF_7'(A_154, B_155)) | '#skF_1'(k1_tarski(B_155), '#skF_8')=B_155 | k1_xboole_0=A_154)), inference(resolution, [status(thm)], [c_76, c_716])).
% 4.11/1.74  tff(c_1469, plain, (![A_184, B_185]: (k1_relat_1('#skF_7'(A_184, B_185))!='#skF_9' | '#skF_1'(k1_tarski(B_185), '#skF_8')=B_185 | k1_xboole_0=A_184)), inference(resolution, [status(thm)], [c_74, c_1068])).
% 4.11/1.74  tff(c_1472, plain, (![A_34, B_38]: (A_34!='#skF_9' | '#skF_1'(k1_tarski(B_38), '#skF_8')=B_38 | k1_xboole_0=A_34 | k1_xboole_0=A_34)), inference(superposition, [status(thm), theory('equality')], [c_72, c_1469])).
% 4.11/1.74  tff(c_1643, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1472])).
% 4.11/1.74  tff(c_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.11/1.74  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.11/1.74  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.11/1.74  tff(c_181, plain, (![C_61]: (~r1_tarski(k2_relat_1(C_61), '#skF_8') | k1_relat_1(C_61)!='#skF_9' | ~v1_funct_1(C_61) | ~v1_relat_1(C_61))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.11/1.74  tff(c_184, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_181])).
% 4.11/1.74  tff(c_186, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_28, c_184])).
% 4.11/1.74  tff(c_187, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_186])).
% 4.11/1.74  tff(c_64, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.11/1.74  tff(c_68, plain, (![A_28]: (v1_relat_1('#skF_6'(A_28)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.11/1.74  tff(c_203, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.11/1.74  tff(c_209, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))!=k1_xboole_0 | '#skF_6'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_203])).
% 4.11/1.74  tff(c_214, plain, (![A_65]: (k1_xboole_0!=A_65 | '#skF_6'(A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_209])).
% 4.11/1.74  tff(c_224, plain, (![A_65]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_214, c_68])).
% 4.11/1.74  tff(c_230, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(negUnitSimplification, [status(thm)], [c_187, c_224])).
% 4.11/1.74  tff(c_48, plain, (![B_22]: (k2_zfmisc_1(k1_xboole_0, B_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.11/1.74  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_48])).
% 4.11/1.74  tff(c_252, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_186])).
% 4.11/1.74  tff(c_254, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_252])).
% 4.11/1.74  tff(c_1686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1643, c_254])).
% 4.11/1.74  tff(c_1689, plain, (![B_199]: ('#skF_1'(k1_tarski(B_199), '#skF_8')=B_199)), inference(splitRight, [status(thm)], [c_1472])).
% 4.11/1.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.74  tff(c_1723, plain, (![B_200]: (~r2_hidden(B_200, '#skF_8') | r1_tarski(k1_tarski(B_200), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1689, c_4])).
% 4.11/1.74  tff(c_1731, plain, (![A_201, B_202]: (k1_relat_1('#skF_7'(A_201, B_202))!='#skF_9' | ~v1_funct_1('#skF_7'(A_201, B_202)) | ~v1_relat_1('#skF_7'(A_201, B_202)) | k1_xboole_0=A_201 | ~r2_hidden(B_202, '#skF_8'))), inference(resolution, [status(thm)], [c_1723, c_546])).
% 4.11/1.74  tff(c_2113, plain, (![A_225, B_226]: (k1_relat_1('#skF_7'(A_225, B_226))!='#skF_9' | ~v1_funct_1('#skF_7'(A_225, B_226)) | ~r2_hidden(B_226, '#skF_8') | k1_xboole_0=A_225)), inference(resolution, [status(thm)], [c_76, c_1731])).
% 4.11/1.74  tff(c_2118, plain, (![A_227, B_228]: (k1_relat_1('#skF_7'(A_227, B_228))!='#skF_9' | ~r2_hidden(B_228, '#skF_8') | k1_xboole_0=A_227)), inference(resolution, [status(thm)], [c_74, c_2113])).
% 4.11/1.74  tff(c_2121, plain, (![A_34, B_38]: (A_34!='#skF_9' | ~r2_hidden(B_38, '#skF_8') | k1_xboole_0=A_34 | k1_xboole_0=A_34)), inference(superposition, [status(thm), theory('equality')], [c_72, c_2118])).
% 4.11/1.74  tff(c_2123, plain, (![B_229]: (~r2_hidden(B_229, '#skF_8'))), inference(splitLeft, [status(thm)], [c_2121])).
% 4.11/1.74  tff(c_2131, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1987, c_2123])).
% 4.11/1.74  tff(c_2204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_2131])).
% 4.11/1.74  tff(c_2206, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_2121])).
% 4.11/1.74  tff(c_2254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2206, c_254])).
% 4.11/1.74  tff(c_2256, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_252])).
% 4.11/1.74  tff(c_2255, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_252])).
% 4.11/1.74  tff(c_2275, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2255])).
% 4.11/1.74  tff(c_2257, plain, (![A_230]: (k1_relat_1(A_230)!=k1_xboole_0 | k1_xboole_0=A_230 | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.11/1.74  tff(c_2266, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))!=k1_xboole_0 | '#skF_6'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_2257])).
% 4.11/1.74  tff(c_2273, plain, (![A_28]: (k1_xboole_0!=A_28 | '#skF_6'(A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2266])).
% 4.11/1.74  tff(c_2358, plain, (![A_238]: (A_238!='#skF_9' | '#skF_6'(A_238)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_2273])).
% 4.11/1.74  tff(c_66, plain, (![A_28]: (v1_funct_1('#skF_6'(A_28)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.11/1.74  tff(c_2366, plain, (![A_238]: (v1_funct_1('#skF_9') | A_238!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2358, c_66])).
% 4.11/1.74  tff(c_2374, plain, (![A_238]: (A_238!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2275, c_2366])).
% 4.11/1.74  tff(c_2282, plain, (![A_21]: (k2_zfmisc_1(A_21, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2256, c_2256, c_46])).
% 4.11/1.74  tff(c_2384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2374, c_2282])).
% 4.11/1.74  tff(c_2386, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 4.11/1.74  tff(c_2385, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_80])).
% 4.11/1.74  tff(c_2396, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_2385])).
% 4.11/1.74  tff(c_2391, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_2385, c_56])).
% 4.11/1.74  tff(c_2412, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2396, c_2396, c_2391])).
% 4.11/1.74  tff(c_2390, plain, (![A_13]: (r1_tarski('#skF_9', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_28])).
% 4.11/1.74  tff(c_2410, plain, (![A_13]: (r1_tarski('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2396, c_2390])).
% 4.11/1.74  tff(c_2389, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_2385, c_54])).
% 4.11/1.74  tff(c_2405, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2396, c_2396, c_2389])).
% 4.11/1.74  tff(c_2450, plain, (![C_243]: (~r1_tarski(k2_relat_1(C_243), '#skF_8') | k1_relat_1(C_243)!='#skF_8' | ~v1_funct_1(C_243) | ~v1_relat_1(C_243))), inference(demodulation, [status(thm), theory('equality')], [c_2396, c_78])).
% 4.11/1.74  tff(c_2453, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2405, c_2450])).
% 4.11/1.74  tff(c_2455, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2410, c_2453])).
% 4.11/1.74  tff(c_2456, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2455])).
% 4.11/1.74  tff(c_60, plain, (![A_27]: (k1_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.11/1.74  tff(c_2509, plain, (![A_255]: (k1_relat_1(A_255)!='#skF_8' | A_255='#skF_8' | ~v1_relat_1(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_2386, c_60])).
% 4.11/1.74  tff(c_2515, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))!='#skF_8' | '#skF_6'(A_28)='#skF_8')), inference(resolution, [status(thm)], [c_68, c_2509])).
% 4.11/1.74  tff(c_2520, plain, (![A_256]: (A_256!='#skF_8' | '#skF_6'(A_256)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2515])).
% 4.11/1.74  tff(c_2530, plain, (![A_256]: (v1_relat_1('#skF_8') | A_256!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2520, c_68])).
% 4.11/1.74  tff(c_2536, plain, (![A_256]: (A_256!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2456, c_2530])).
% 4.11/1.74  tff(c_2388, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_2385, c_26])).
% 4.11/1.74  tff(c_2441, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2396, c_2396, c_2388])).
% 4.11/1.74  tff(c_2549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2536, c_2441])).
% 4.11/1.74  tff(c_2550, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_2455])).
% 4.11/1.74  tff(c_2636, plain, (![A_271]: (k1_relat_1(A_271)!='#skF_8' | A_271='#skF_8' | ~v1_relat_1(A_271))), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_2386, c_60])).
% 4.11/1.74  tff(c_2645, plain, (![A_28]: (k1_relat_1('#skF_6'(A_28))!='#skF_8' | '#skF_6'(A_28)='#skF_8')), inference(resolution, [status(thm)], [c_68, c_2636])).
% 4.11/1.74  tff(c_2654, plain, (![A_272]: (A_272!='#skF_8' | '#skF_6'(A_272)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2645])).
% 4.11/1.74  tff(c_2662, plain, (![A_272]: (v1_funct_1('#skF_8') | A_272!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2654, c_66])).
% 4.11/1.74  tff(c_2670, plain, (![A_272]: (A_272!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2550, c_2662])).
% 4.11/1.74  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2670, c_2441])).
% 4.11/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.74  
% 4.11/1.74  Inference rules
% 4.11/1.74  ----------------------
% 4.11/1.74  #Ref     : 0
% 4.11/1.74  #Sup     : 554
% 4.11/1.74  #Fact    : 0
% 4.11/1.74  #Define  : 0
% 4.11/1.74  #Split   : 7
% 4.11/1.74  #Chain   : 0
% 4.11/1.74  #Close   : 0
% 4.11/1.74  
% 4.11/1.74  Ordering : KBO
% 4.11/1.74  
% 4.11/1.74  Simplification rules
% 4.11/1.74  ----------------------
% 4.11/1.74  #Subsume      : 88
% 4.11/1.74  #Demod        : 353
% 4.11/1.74  #Tautology    : 271
% 4.11/1.74  #SimpNegUnit  : 79
% 4.11/1.74  #BackRed      : 146
% 4.11/1.74  
% 4.11/1.74  #Partial instantiations: 0
% 4.11/1.74  #Strategies tried      : 1
% 4.11/1.74  
% 4.11/1.74  Timing (in seconds)
% 4.11/1.74  ----------------------
% 4.11/1.75  Preprocessing        : 0.34
% 4.11/1.75  Parsing              : 0.18
% 4.11/1.75  CNF conversion       : 0.03
% 4.11/1.75  Main loop            : 0.60
% 4.11/1.75  Inferencing          : 0.21
% 4.11/1.75  Reduction            : 0.20
% 4.11/1.75  Demodulation         : 0.14
% 4.11/1.75  BG Simplification    : 0.03
% 4.11/1.75  Subsumption          : 0.11
% 4.11/1.75  Abstraction          : 0.03
% 4.11/1.75  MUC search           : 0.00
% 4.11/1.75  Cooper               : 0.00
% 4.11/1.75  Total                : 0.99
% 4.11/1.75  Index Insertion      : 0.00
% 4.11/1.75  Index Deletion       : 0.00
% 4.11/1.75  Index Matching       : 0.00
% 4.11/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
