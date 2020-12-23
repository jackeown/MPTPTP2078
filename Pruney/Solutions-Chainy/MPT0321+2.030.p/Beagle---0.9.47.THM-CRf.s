%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:17 EST 2020

% Result     : Theorem 36.39s
% Output     : CNFRefutation 36.39s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 868 expanded)
%              Number of leaves         :   36 ( 297 expanded)
%              Depth                    :   19
%              Number of atoms          :  319 (1763 expanded)
%              Number of equality atoms :  152 ( 976 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_94,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_80,plain,
    ( '#skF_11' != '#skF_9'
    | '#skF_10' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_90,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( r2_xboole_0(A_22,B_23)
      | B_23 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_7'(A_24,B_25),B_25)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_31] : k4_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_165,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_177,plain,(
    ! [D_60,A_61] :
      ( ~ r2_hidden(D_60,A_61)
      | ~ r2_hidden(D_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_165])).

tff(c_195,plain,(
    ! [A_66] :
      ( ~ r2_hidden('#skF_1'(A_66),k1_xboole_0)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_200,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_195])).

tff(c_86,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_201,plain,(
    ! [B_67,A_68] :
      ( k1_xboole_0 = B_67
      | k1_xboole_0 = A_68
      | k2_zfmisc_1(A_68,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_201])).

tff(c_275,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_62,plain,(
    ! [B_28] : r1_tarski(B_28,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_131,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_135,plain,(
    ! [B_28] : k3_xboole_0(B_28,B_28) = B_28 ),
    inference(resolution,[status(thm)],[c_62,c_131])).

tff(c_70,plain,(
    ! [A_32] : k2_zfmisc_1(A_32,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_436,plain,(
    ! [D_101,A_102,B_103] :
      ( r2_hidden(D_101,A_102)
      | ~ r2_hidden(D_101,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2212,plain,(
    ! [A_204,B_205] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_204,B_205)),A_204)
      | v1_xboole_0(k3_xboole_0(A_204,B_205)) ) ),
    inference(resolution,[status(thm)],[c_4,c_436])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2279,plain,(
    ! [A_206,B_207] :
      ( ~ v1_xboole_0(A_206)
      | v1_xboole_0(k3_xboole_0(A_206,B_207)) ) ),
    inference(resolution,[status(thm)],[c_2212,c_2])).

tff(c_232,plain,(
    ! [D_72,B_73,A_74] :
      ( r2_hidden(D_72,B_73)
      | ~ r2_hidden(D_72,k3_xboole_0(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_585,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_118,B_119)),B_119)
      | v1_xboole_0(k3_xboole_0(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_726,plain,(
    ! [B_125,A_126] :
      ( ~ v1_xboole_0(B_125)
      | v1_xboole_0(k3_xboole_0(A_126,B_125)) ) ),
    inference(resolution,[status(thm)],[c_585,c_2])).

tff(c_276,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_305,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(A_83)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_276,c_2])).

tff(c_252,plain,(
    ! [A_77,B_78] :
      ( r2_xboole_0(A_77,B_78)
      | B_78 = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_181,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_7'(A_62,B_63),B_63)
      | ~ r2_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    ! [B_63,A_62] :
      ( ~ v1_xboole_0(B_63)
      | ~ r2_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_263,plain,(
    ! [B_78,A_77] :
      ( ~ v1_xboole_0(B_78)
      | B_78 = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_252,c_193])).

tff(c_348,plain,(
    ! [B_90,A_91] :
      ( ~ v1_xboole_0(B_90)
      | B_90 = A_91
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_305,c_263])).

tff(c_351,plain,(
    ! [A_91] :
      ( k1_xboole_0 = A_91
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_200,c_348])).

tff(c_743,plain,(
    ! [A_126,B_125] :
      ( k3_xboole_0(A_126,B_125) = k1_xboole_0
      | ~ v1_xboole_0(B_125) ) ),
    inference(resolution,[status(thm)],[c_726,c_351])).

tff(c_2459,plain,(
    ! [A_216,A_217,B_218] :
      ( k3_xboole_0(A_216,k3_xboole_0(A_217,B_218)) = k1_xboole_0
      | ~ v1_xboole_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_2279,c_743])).

tff(c_74,plain,(
    ! [A_34,C_36,B_35,D_37] : k3_xboole_0(k2_zfmisc_1(A_34,C_36),k2_zfmisc_1(B_35,D_37)) = k2_zfmisc_1(k3_xboole_0(A_34,B_35),k3_xboole_0(C_36,D_37)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_766,plain,(
    ! [A_132,C_133,B_134,D_135] : k3_xboole_0(k2_zfmisc_1(A_132,C_133),k2_zfmisc_1(B_134,D_135)) = k2_zfmisc_1(k3_xboole_0(A_132,B_134),k3_xboole_0(C_133,D_135)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_798,plain,(
    ! [B_134,D_135] : k3_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'),k2_zfmisc_1(B_134,D_135)) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_134),k3_xboole_0('#skF_11',D_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_766])).

tff(c_917,plain,(
    ! [B_145,D_146] : k2_zfmisc_1(k3_xboole_0('#skF_10',B_145),k3_xboole_0('#skF_11',D_146)) = k2_zfmisc_1(k3_xboole_0('#skF_8',B_145),k3_xboole_0('#skF_9',D_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_798])).

tff(c_952,plain,(
    ! [D_146] : k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_10'),k3_xboole_0('#skF_9',D_146)) = k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',D_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_917])).

tff(c_2478,plain,(
    ! [A_217,B_218] :
      ( k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k3_xboole_0(A_217,B_218))) = k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_10'),k1_xboole_0)
      | ~ v1_xboole_0(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2459,c_952])).

tff(c_6014,plain,(
    ! [A_339,B_340] :
      ( k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k3_xboole_0(A_339,B_340))) = k1_xboole_0
      | ~ v1_xboole_0(A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2478])).

tff(c_6126,plain,(
    ! [B_344] :
      ( k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',B_344)) = k1_xboole_0
      | ~ v1_xboole_0(B_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6014])).

tff(c_6180,plain,
    ( k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0
    | ~ v1_xboole_0('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6126])).

tff(c_6197,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0
    | ~ v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6180])).

tff(c_6198,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_6197])).

tff(c_72,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_372,plain,(
    ! [B_95,A_96] :
      ( ~ r2_hidden(B_95,A_96)
      | k4_xboole_0(A_96,k1_tarski(B_95)) != A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_381,plain,(
    ! [B_95] : ~ r2_hidden(B_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_372])).

tff(c_2338,plain,(
    ! [A_208,B_209,C_210] :
      ( r2_hidden('#skF_3'(A_208,B_209,C_210),A_208)
      | r2_hidden('#skF_4'(A_208,B_209,C_210),C_210)
      | k3_xboole_0(A_208,B_209) = C_210 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2403,plain,(
    ! [A_208,B_209] :
      ( r2_hidden('#skF_3'(A_208,B_209,k1_xboole_0),A_208)
      | k3_xboole_0(A_208,B_209) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2338,c_381])).

tff(c_1748,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden('#skF_3'(A_187,B_188,C_189),B_188)
      | r2_hidden('#skF_4'(A_187,B_188,C_189),C_189)
      | k3_xboole_0(A_187,B_188) = C_189 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [D_21,B_17,A_16] :
      ( ~ r2_hidden(D_21,B_17)
      | ~ r2_hidden(D_21,k4_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73639,plain,(
    ! [A_1226,A_1227,B_1228,C_1229] :
      ( ~ r2_hidden('#skF_3'(A_1226,k4_xboole_0(A_1227,B_1228),C_1229),B_1228)
      | r2_hidden('#skF_4'(A_1226,k4_xboole_0(A_1227,B_1228),C_1229),C_1229)
      | k3_xboole_0(A_1226,k4_xboole_0(A_1227,B_1228)) = C_1229 ) ),
    inference(resolution,[status(thm)],[c_1748,c_32])).

tff(c_73691,plain,(
    ! [A_208,A_1227] :
      ( r2_hidden('#skF_4'(A_208,k4_xboole_0(A_1227,A_208),k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_208,k4_xboole_0(A_1227,A_208)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2403,c_73639])).

tff(c_73732,plain,(
    ! [A_1230,A_1231] : k3_xboole_0(A_1230,k4_xboole_0(A_1231,A_1230)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_73691])).

tff(c_956,plain,(
    ! [B_145] : k2_zfmisc_1(k3_xboole_0('#skF_8',B_145),k3_xboole_0('#skF_9','#skF_11')) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_145),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_917])).

tff(c_74477,plain,(
    ! [A_1231] : k2_zfmisc_1(k3_xboole_0('#skF_10',k4_xboole_0(A_1231,'#skF_8')),'#skF_11') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_9','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73732,c_956])).

tff(c_74943,plain,(
    ! [A_1232] : k2_zfmisc_1(k3_xboole_0('#skF_10',k4_xboole_0(A_1232,'#skF_8')),'#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74477])).

tff(c_68,plain,(
    ! [B_33,A_32] :
      ( k1_xboole_0 = B_33
      | k1_xboole_0 = A_32
      | k2_zfmisc_1(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_75071,plain,(
    ! [A_1232] :
      ( k1_xboole_0 = '#skF_11'
      | k3_xboole_0('#skF_10',k4_xboole_0(A_1232,'#skF_8')) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74943,c_68])).

tff(c_77086,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_75071])).

tff(c_77282,plain,(
    v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77086,c_200])).

tff(c_77289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6198,c_77282])).

tff(c_77291,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_75071])).

tff(c_34,plain,(
    ! [D_21,A_16,B_17] :
      ( r2_hidden(D_21,A_16)
      | ~ r2_hidden(D_21,k4_xboole_0(A_16,B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21908,plain,(
    ! [A_715,B_716,B_717] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_715,B_716),B_717),A_715)
      | r1_tarski(k4_xboole_0(A_715,B_716),B_717) ) ),
    inference(resolution,[status(thm)],[c_276,c_34])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22016,plain,(
    ! [A_718,B_719] : r1_tarski(k4_xboole_0(A_718,B_719),A_718) ),
    inference(resolution,[status(thm)],[c_21908,c_8])).

tff(c_64,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22134,plain,(
    ! [A_718,B_719] : k3_xboole_0(k4_xboole_0(A_718,B_719),A_718) = k4_xboole_0(A_718,B_719) ),
    inference(resolution,[status(thm)],[c_22016,c_64])).

tff(c_1813,plain,(
    ! [A_187,B_188] :
      ( r2_hidden('#skF_3'(A_187,B_188,k1_xboole_0),B_188)
      | k3_xboole_0(A_187,B_188) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1748,c_381])).

tff(c_92917,plain,(
    ! [A_1370,B_1371,B_1372,C_1373] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_1370,B_1371),B_1372,C_1373),B_1371)
      | r2_hidden('#skF_4'(k4_xboole_0(A_1370,B_1371),B_1372,C_1373),C_1373)
      | k3_xboole_0(k4_xboole_0(A_1370,B_1371),B_1372) = C_1373 ) ),
    inference(resolution,[status(thm)],[c_2338,c_32])).

tff(c_92984,plain,(
    ! [A_1370,B_188] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_1370,B_188),B_188,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_1370,B_188),B_188) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1813,c_92917])).

tff(c_93030,plain,(
    ! [A_1374,B_1375] : k3_xboole_0(k4_xboole_0(A_1374,B_1375),B_1375) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_92984])).

tff(c_801,plain,(
    ! [A_132,C_133] : k3_xboole_0(k2_zfmisc_1(A_132,C_133),k2_zfmisc_1('#skF_8','#skF_9')) = k2_zfmisc_1(k3_xboole_0(A_132,'#skF_10'),k3_xboole_0(C_133,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_766])).

tff(c_1218,plain,(
    ! [A_162,C_163] : k2_zfmisc_1(k3_xboole_0(A_162,'#skF_10'),k3_xboole_0(C_163,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_162,'#skF_8'),k3_xboole_0(C_163,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_801])).

tff(c_1257,plain,(
    ! [A_162] : k2_zfmisc_1(k3_xboole_0(A_162,'#skF_8'),k3_xboole_0('#skF_11','#skF_9')) = k2_zfmisc_1(k3_xboole_0(A_162,'#skF_10'),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1218])).

tff(c_93837,plain,(
    ! [A_1374] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1374,'#skF_8'),'#skF_10'),'#skF_11') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_11','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93030,c_1257])).

tff(c_94348,plain,(
    ! [A_1376] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1376,'#skF_8'),'#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93837])).

tff(c_94424,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_10','#skF_8'),'#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22134,c_94348])).

tff(c_94521,plain,
    ( k1_xboole_0 = '#skF_11'
    | k4_xboole_0('#skF_10','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94424,c_68])).

tff(c_94534,plain,(
    k4_xboole_0('#skF_10','#skF_8') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77291,c_94521])).

tff(c_693,plain,(
    ! [D_122,A_123,B_124] :
      ( r2_hidden(D_122,k4_xboole_0(A_123,B_124))
      | r2_hidden(D_122,B_124)
      | ~ r2_hidden(D_122,A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_724,plain,(
    ! [A_123,B_124,D_122] :
      ( ~ v1_xboole_0(k4_xboole_0(A_123,B_124))
      | r2_hidden(D_122,B_124)
      | ~ r2_hidden(D_122,A_123) ) ),
    inference(resolution,[status(thm)],[c_693,c_2])).

tff(c_94823,plain,(
    ! [D_122] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_122,'#skF_8')
      | ~ r2_hidden(D_122,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94534,c_724])).

tff(c_95754,plain,(
    ! [D_1378] :
      ( r2_hidden(D_1378,'#skF_8')
      | ~ r2_hidden(D_1378,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_94823])).

tff(c_108244,plain,(
    ! [A_1462] :
      ( r2_hidden('#skF_7'(A_1462,'#skF_10'),'#skF_8')
      | ~ r2_xboole_0(A_1462,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_56,c_95754])).

tff(c_54,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden('#skF_7'(A_24,B_25),A_24)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108266,plain,(
    ~ r2_xboole_0('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_108244,c_54])).

tff(c_108270,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_108266])).

tff(c_108273,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_108270])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_820,plain,(
    ! [A_132,C_133] : k2_zfmisc_1(k3_xboole_0(A_132,'#skF_10'),k3_xboole_0(C_133,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_132,'#skF_8'),k3_xboole_0(C_133,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_801])).

tff(c_93884,plain,(
    ! [A_1374,C_133] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1374,'#skF_10'),'#skF_8'),k3_xboole_0(C_133,'#skF_9')) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(C_133,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93030,c_820])).

tff(c_113951,plain,(
    ! [A_1535,C_1536] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1535,'#skF_10'),'#skF_8'),k3_xboole_0(C_1536,'#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93884])).

tff(c_114277,plain,(
    ! [C_1537] : k2_zfmisc_1(k4_xboole_0('#skF_8','#skF_10'),k3_xboole_0(C_1537,'#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22134,c_113951])).

tff(c_114381,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_8','#skF_10'),'#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_114277])).

tff(c_114421,plain,
    ( k1_xboole_0 = '#skF_9'
    | k4_xboole_0('#skF_8','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_114381,c_68])).

tff(c_114434,plain,(
    k4_xboole_0('#skF_8','#skF_10') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_114421])).

tff(c_114734,plain,(
    ! [D_122] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_122,'#skF_10')
      | ~ r2_hidden(D_122,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114434,c_724])).

tff(c_114842,plain,(
    ! [D_1538] :
      ( r2_hidden(D_1538,'#skF_10')
      | ~ r2_hidden(D_1538,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_114734])).

tff(c_116133,plain,(
    ! [A_1545] :
      ( r1_tarski(A_1545,'#skF_10')
      | ~ r2_hidden('#skF_2'(A_1545,'#skF_10'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_114842,c_8])).

tff(c_116157,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_116133])).

tff(c_116167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108273,c_108273,c_116157])).

tff(c_116168,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_116170,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_116168])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_116179,plain,(
    '#skF_11' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_84])).

tff(c_116178,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_82])).

tff(c_116169,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_116210,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_116169])).

tff(c_116412,plain,(
    ! [B_1573,A_1574] :
      ( B_1573 = '#skF_11'
      | A_1574 = '#skF_11'
      | k2_zfmisc_1(A_1574,B_1573) != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116170,c_116170,c_116170,c_68])).

tff(c_116421,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_116210,c_116412])).

tff(c_116429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116179,c_116178,c_116421])).

tff(c_116430,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_116168])).

tff(c_116439,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116430,c_82])).

tff(c_116468,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116430,c_116169])).

tff(c_116678,plain,(
    ! [B_1602,A_1603] :
      ( B_1602 = '#skF_10'
      | A_1603 = '#skF_10'
      | k2_zfmisc_1(A_1603,B_1602) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116430,c_116430,c_116430,c_68])).

tff(c_116684,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_116468,c_116678])).

tff(c_116693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_116439,c_116684])).

tff(c_116694,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_116956,plain,(
    ! [B_1653,A_1654] :
      ( ~ r2_hidden(B_1653,A_1654)
      | k4_xboole_0(A_1654,k1_tarski(B_1653)) != A_1654 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_116965,plain,(
    ! [B_1653] : ~ r2_hidden(B_1653,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_116956])).

tff(c_118871,plain,(
    ! [A_1766,B_1767,C_1768] :
      ( r2_hidden('#skF_3'(A_1766,B_1767,C_1768),B_1767)
      | r2_hidden('#skF_4'(A_1766,B_1767,C_1768),C_1768)
      | k3_xboole_0(A_1766,B_1767) = C_1768 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118936,plain,(
    ! [A_1766,B_1767] :
      ( r2_hidden('#skF_3'(A_1766,B_1767,k1_xboole_0),B_1767)
      | k3_xboole_0(A_1766,B_1767) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_118871,c_116965])).

tff(c_117864,plain,(
    ! [A_1725,B_1726,C_1727] :
      ( r2_hidden('#skF_3'(A_1725,B_1726,C_1727),A_1725)
      | r2_hidden('#skF_4'(A_1725,B_1726,C_1727),C_1727)
      | k3_xboole_0(A_1725,B_1726) = C_1727 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185497,plain,(
    ! [A_2774,B_2775,B_2776,C_2777] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_2774,B_2775),B_2776,C_2777),B_2775)
      | r2_hidden('#skF_4'(k4_xboole_0(A_2774,B_2775),B_2776,C_2777),C_2777)
      | k3_xboole_0(k4_xboole_0(A_2774,B_2775),B_2776) = C_2777 ) ),
    inference(resolution,[status(thm)],[c_117864,c_32])).

tff(c_185554,plain,(
    ! [A_2774,B_1767] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_2774,B_1767),B_1767,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_2774,B_1767),B_1767) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_118936,c_185497])).

tff(c_185595,plain,(
    ! [A_2778,B_2779] : k3_xboole_0(k4_xboole_0(A_2778,B_2779),B_2779) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_116965,c_185554])).

tff(c_116745,plain,(
    ! [A_1612,B_1613] :
      ( k3_xboole_0(A_1612,B_1613) = A_1612
      | ~ r1_tarski(A_1612,B_1613) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116749,plain,(
    ! [B_28] : k3_xboole_0(B_28,B_28) = B_28 ),
    inference(resolution,[status(thm)],[c_62,c_116745])).

tff(c_116695,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_116700,plain,(
    k2_zfmisc_1('#skF_8','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116695,c_86])).

tff(c_117397,plain,(
    ! [A_1696,C_1697,B_1698,D_1699] : k3_xboole_0(k2_zfmisc_1(A_1696,C_1697),k2_zfmisc_1(B_1698,D_1699)) = k2_zfmisc_1(k3_xboole_0(A_1696,B_1698),k3_xboole_0(C_1697,D_1699)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_117428,plain,(
    ! [A_1696,C_1697] : k3_xboole_0(k2_zfmisc_1(A_1696,C_1697),k2_zfmisc_1('#skF_8','#skF_9')) = k2_zfmisc_1(k3_xboole_0(A_1696,'#skF_8'),k3_xboole_0(C_1697,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116700,c_117397])).

tff(c_117514,plain,(
    ! [A_1701,C_1702] : k2_zfmisc_1(k3_xboole_0(A_1701,'#skF_8'),k3_xboole_0(C_1702,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_1701,'#skF_8'),k3_xboole_0(C_1702,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117428])).

tff(c_119027,plain,(
    ! [C_1773,A_1774] :
      ( k3_xboole_0(C_1773,'#skF_11') = k1_xboole_0
      | k3_xboole_0(A_1774,'#skF_8') = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(A_1774,'#skF_8'),k3_xboole_0(C_1773,'#skF_9')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117514,c_68])).

tff(c_119078,plain,(
    ! [C_1773] :
      ( k3_xboole_0(C_1773,'#skF_11') = k1_xboole_0
      | k3_xboole_0('#skF_8','#skF_8') = k1_xboole_0
      | k2_zfmisc_1('#skF_8',k3_xboole_0(C_1773,'#skF_9')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116749,c_119027])).

tff(c_119102,plain,(
    ! [C_1773] :
      ( k3_xboole_0(C_1773,'#skF_11') = k1_xboole_0
      | k1_xboole_0 = '#skF_8'
      | k2_zfmisc_1('#skF_8',k3_xboole_0(C_1773,'#skF_9')) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116749,c_119078])).

tff(c_119103,plain,(
    ! [C_1773] :
      ( k3_xboole_0(C_1773,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_8',k3_xboole_0(C_1773,'#skF_9')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_119102])).

tff(c_186309,plain,(
    ! [A_2778] :
      ( k3_xboole_0(k4_xboole_0(A_2778,'#skF_9'),'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_8',k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185595,c_119103])).

tff(c_186804,plain,(
    ! [A_2780] : k3_xboole_0(k4_xboole_0(A_2780,'#skF_9'),'#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_186309])).

tff(c_116934,plain,(
    ! [D_1650,A_1651,B_1652] :
      ( r2_hidden(D_1650,A_1651)
      | ~ r2_hidden(D_1650,k4_xboole_0(A_1651,B_1652)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133124,plain,(
    ! [A_2148,B_2149,B_2150] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_2148,B_2149),B_2150),A_2148)
      | r1_tarski(k4_xboole_0(A_2148,B_2149),B_2150) ) ),
    inference(resolution,[status(thm)],[c_10,c_116934])).

tff(c_133232,plain,(
    ! [A_2151,B_2152] : r1_tarski(k4_xboole_0(A_2151,B_2152),A_2151) ),
    inference(resolution,[status(thm)],[c_133124,c_8])).

tff(c_133337,plain,(
    ! [A_2151,B_2152] : k3_xboole_0(k4_xboole_0(A_2151,B_2152),A_2151) = k4_xboole_0(A_2151,B_2152) ),
    inference(resolution,[status(thm)],[c_133232,c_64])).

tff(c_187070,plain,(
    k4_xboole_0('#skF_11','#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_186804,c_133337])).

tff(c_30,plain,(
    ! [D_21,A_16,B_17] :
      ( r2_hidden(D_21,k4_xboole_0(A_16,B_17))
      | r2_hidden(D_21,B_17)
      | ~ r2_hidden(D_21,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_187737,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,k1_xboole_0)
      | r2_hidden(D_21,'#skF_9')
      | ~ r2_hidden(D_21,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187070,c_30])).

tff(c_188049,plain,(
    ! [D_2784] :
      ( r2_hidden(D_2784,'#skF_9')
      | ~ r2_hidden(D_2784,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_116965,c_187737])).

tff(c_195132,plain,(
    ! [A_2834] :
      ( r2_hidden('#skF_7'(A_2834,'#skF_11'),'#skF_9')
      | ~ r2_xboole_0(A_2834,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_56,c_188049])).

tff(c_195151,plain,(
    ~ r2_xboole_0('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_195132,c_54])).

tff(c_195155,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_48,c_195151])).

tff(c_195158,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_116694,c_195155])).

tff(c_117541,plain,(
    ! [C_1702] : k2_zfmisc_1(k3_xboole_0('#skF_8','#skF_8'),k3_xboole_0(C_1702,'#skF_9')) = k2_zfmisc_1('#skF_8',k3_xboole_0(C_1702,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116749,c_117514])).

tff(c_117552,plain,(
    ! [C_1702] : k2_zfmisc_1('#skF_8',k3_xboole_0(C_1702,'#skF_11')) = k2_zfmisc_1('#skF_8',k3_xboole_0(C_1702,'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116749,c_117541])).

tff(c_186281,plain,(
    ! [A_2778] : k2_zfmisc_1('#skF_8',k3_xboole_0(k4_xboole_0(A_2778,'#skF_11'),'#skF_9')) = k2_zfmisc_1('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_185595,c_117552])).

tff(c_190821,plain,(
    ! [A_2812] : k2_zfmisc_1('#skF_8',k3_xboole_0(k4_xboole_0(A_2812,'#skF_11'),'#skF_9')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_186281])).

tff(c_190850,plain,(
    ! [A_2812] :
      ( k3_xboole_0(k4_xboole_0(A_2812,'#skF_11'),'#skF_9') = k1_xboole_0
      | k1_xboole_0 = '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190821,c_68])).

tff(c_190989,plain,(
    ! [A_2813] : k3_xboole_0(k4_xboole_0(A_2813,'#skF_11'),'#skF_9') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_190850])).

tff(c_191283,plain,(
    k4_xboole_0('#skF_9','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190989,c_133337])).

tff(c_192057,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,k1_xboole_0)
      | r2_hidden(D_21,'#skF_11')
      | ~ r2_hidden(D_21,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191283,c_30])).

tff(c_192187,plain,(
    ! [D_2814] :
      ( r2_hidden(D_2814,'#skF_11')
      | ~ r2_hidden(D_2814,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_116965,c_192057])).

tff(c_196247,plain,(
    ! [A_2842] :
      ( r1_tarski(A_2842,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_2842,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_192187,c_8])).

tff(c_196271,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_196247])).

tff(c_196281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195158,c_195158,c_196271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.39/24.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/24.72  
% 36.39/24.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/24.72  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7
% 36.39/24.72  
% 36.39/24.72  %Foreground sorts:
% 36.39/24.72  
% 36.39/24.72  
% 36.39/24.72  %Background operators:
% 36.39/24.72  
% 36.39/24.72  
% 36.39/24.72  %Foreground operators:
% 36.39/24.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.39/24.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.39/24.72  tff('#skF_11', type, '#skF_11': $i).
% 36.39/24.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 36.39/24.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.39/24.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.39/24.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 36.39/24.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.39/24.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 36.39/24.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.39/24.72  tff('#skF_10', type, '#skF_10': $i).
% 36.39/24.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.39/24.72  tff('#skF_9', type, '#skF_9': $i).
% 36.39/24.72  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 36.39/24.72  tff('#skF_8', type, '#skF_8': $i).
% 36.39/24.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.39/24.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.39/24.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.39/24.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.39/24.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.39/24.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.39/24.72  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 36.39/24.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.39/24.72  
% 36.39/24.75  tff(f_110, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 36.39/24.75  tff(f_64, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 36.39/24.75  tff(f_74, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 36.39/24.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 36.39/24.75  tff(f_86, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 36.39/24.75  tff(f_57, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 36.39/24.75  tff(f_92, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 36.39/24.75  tff(f_80, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.39/24.75  tff(f_84, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.39/24.75  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 36.39/24.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 36.39/24.75  tff(f_94, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 36.39/24.75  tff(f_99, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 36.39/24.75  tff(c_80, plain, ('#skF_11'!='#skF_9' | '#skF_10'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.39/24.75  tff(c_90, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_80])).
% 36.39/24.75  tff(c_48, plain, (![A_22, B_23]: (r2_xboole_0(A_22, B_23) | B_23=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.39/24.75  tff(c_56, plain, (![A_24, B_25]: (r2_hidden('#skF_7'(A_24, B_25), B_25) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 36.39/24.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.39/24.75  tff(c_66, plain, (![A_31]: (k4_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_86])).
% 36.39/24.75  tff(c_165, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_177, plain, (![D_60, A_61]: (~r2_hidden(D_60, A_61) | ~r2_hidden(D_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_165])).
% 36.39/24.75  tff(c_195, plain, (![A_66]: (~r2_hidden('#skF_1'(A_66), k1_xboole_0) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_4, c_177])).
% 36.39/24.75  tff(c_200, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_195])).
% 36.39/24.75  tff(c_86, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.39/24.75  tff(c_201, plain, (![B_67, A_68]: (k1_xboole_0=B_67 | k1_xboole_0=A_68 | k2_zfmisc_1(A_68, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 36.39/24.75  tff(c_204, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10' | k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_86, c_201])).
% 36.39/24.75  tff(c_275, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_204])).
% 36.39/24.75  tff(c_62, plain, (![B_28]: (r1_tarski(B_28, B_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 36.39/24.75  tff(c_131, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.39/24.75  tff(c_135, plain, (![B_28]: (k3_xboole_0(B_28, B_28)=B_28)), inference(resolution, [status(thm)], [c_62, c_131])).
% 36.39/24.75  tff(c_70, plain, (![A_32]: (k2_zfmisc_1(A_32, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 36.39/24.75  tff(c_436, plain, (![D_101, A_102, B_103]: (r2_hidden(D_101, A_102) | ~r2_hidden(D_101, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_2212, plain, (![A_204, B_205]: (r2_hidden('#skF_1'(k3_xboole_0(A_204, B_205)), A_204) | v1_xboole_0(k3_xboole_0(A_204, B_205)))), inference(resolution, [status(thm)], [c_4, c_436])).
% 36.39/24.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.39/24.75  tff(c_2279, plain, (![A_206, B_207]: (~v1_xboole_0(A_206) | v1_xboole_0(k3_xboole_0(A_206, B_207)))), inference(resolution, [status(thm)], [c_2212, c_2])).
% 36.39/24.75  tff(c_232, plain, (![D_72, B_73, A_74]: (r2_hidden(D_72, B_73) | ~r2_hidden(D_72, k3_xboole_0(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_585, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(k3_xboole_0(A_118, B_119)), B_119) | v1_xboole_0(k3_xboole_0(A_118, B_119)))), inference(resolution, [status(thm)], [c_4, c_232])).
% 36.39/24.75  tff(c_726, plain, (![B_125, A_126]: (~v1_xboole_0(B_125) | v1_xboole_0(k3_xboole_0(A_126, B_125)))), inference(resolution, [status(thm)], [c_585, c_2])).
% 36.39/24.75  tff(c_276, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.39/24.75  tff(c_305, plain, (![A_83, B_84]: (~v1_xboole_0(A_83) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_276, c_2])).
% 36.39/24.75  tff(c_252, plain, (![A_77, B_78]: (r2_xboole_0(A_77, B_78) | B_78=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.39/24.75  tff(c_181, plain, (![A_62, B_63]: (r2_hidden('#skF_7'(A_62, B_63), B_63) | ~r2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 36.39/24.75  tff(c_193, plain, (![B_63, A_62]: (~v1_xboole_0(B_63) | ~r2_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_181, c_2])).
% 36.39/24.75  tff(c_263, plain, (![B_78, A_77]: (~v1_xboole_0(B_78) | B_78=A_77 | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_252, c_193])).
% 36.39/24.75  tff(c_348, plain, (![B_90, A_91]: (~v1_xboole_0(B_90) | B_90=A_91 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_305, c_263])).
% 36.39/24.75  tff(c_351, plain, (![A_91]: (k1_xboole_0=A_91 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_200, c_348])).
% 36.39/24.75  tff(c_743, plain, (![A_126, B_125]: (k3_xboole_0(A_126, B_125)=k1_xboole_0 | ~v1_xboole_0(B_125))), inference(resolution, [status(thm)], [c_726, c_351])).
% 36.39/24.75  tff(c_2459, plain, (![A_216, A_217, B_218]: (k3_xboole_0(A_216, k3_xboole_0(A_217, B_218))=k1_xboole_0 | ~v1_xboole_0(A_217))), inference(resolution, [status(thm)], [c_2279, c_743])).
% 36.39/24.75  tff(c_74, plain, (![A_34, C_36, B_35, D_37]: (k3_xboole_0(k2_zfmisc_1(A_34, C_36), k2_zfmisc_1(B_35, D_37))=k2_zfmisc_1(k3_xboole_0(A_34, B_35), k3_xboole_0(C_36, D_37)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 36.39/24.75  tff(c_766, plain, (![A_132, C_133, B_134, D_135]: (k3_xboole_0(k2_zfmisc_1(A_132, C_133), k2_zfmisc_1(B_134, D_135))=k2_zfmisc_1(k3_xboole_0(A_132, B_134), k3_xboole_0(C_133, D_135)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 36.39/24.75  tff(c_798, plain, (![B_134, D_135]: (k3_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'), k2_zfmisc_1(B_134, D_135))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_134), k3_xboole_0('#skF_11', D_135)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_766])).
% 36.39/24.75  tff(c_917, plain, (![B_145, D_146]: (k2_zfmisc_1(k3_xboole_0('#skF_10', B_145), k3_xboole_0('#skF_11', D_146))=k2_zfmisc_1(k3_xboole_0('#skF_8', B_145), k3_xboole_0('#skF_9', D_146)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_798])).
% 36.39/24.75  tff(c_952, plain, (![D_146]: (k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_10'), k3_xboole_0('#skF_9', D_146))=k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', D_146)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_917])).
% 36.39/24.75  tff(c_2478, plain, (![A_217, B_218]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k3_xboole_0(A_217, B_218)))=k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_10'), k1_xboole_0) | ~v1_xboole_0(A_217))), inference(superposition, [status(thm), theory('equality')], [c_2459, c_952])).
% 36.39/24.75  tff(c_6014, plain, (![A_339, B_340]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k3_xboole_0(A_339, B_340)))=k1_xboole_0 | ~v1_xboole_0(A_339))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2478])).
% 36.39/24.75  tff(c_6126, plain, (![B_344]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', B_344))=k1_xboole_0 | ~v1_xboole_0(B_344))), inference(superposition, [status(thm), theory('equality')], [c_135, c_6014])).
% 36.39/24.75  tff(c_6180, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0 | ~v1_xboole_0('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_135, c_6126])).
% 36.39/24.75  tff(c_6197, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0 | ~v1_xboole_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6180])).
% 36.39/24.75  tff(c_6198, plain, (~v1_xboole_0('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_275, c_6197])).
% 36.39/24.75  tff(c_72, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 36.39/24.75  tff(c_372, plain, (![B_95, A_96]: (~r2_hidden(B_95, A_96) | k4_xboole_0(A_96, k1_tarski(B_95))!=A_96)), inference(cnfTransformation, [status(thm)], [f_99])).
% 36.39/24.75  tff(c_381, plain, (![B_95]: (~r2_hidden(B_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_372])).
% 36.39/24.75  tff(c_2338, plain, (![A_208, B_209, C_210]: (r2_hidden('#skF_3'(A_208, B_209, C_210), A_208) | r2_hidden('#skF_4'(A_208, B_209, C_210), C_210) | k3_xboole_0(A_208, B_209)=C_210)), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_2403, plain, (![A_208, B_209]: (r2_hidden('#skF_3'(A_208, B_209, k1_xboole_0), A_208) | k3_xboole_0(A_208, B_209)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2338, c_381])).
% 36.39/24.75  tff(c_1748, plain, (![A_187, B_188, C_189]: (r2_hidden('#skF_3'(A_187, B_188, C_189), B_188) | r2_hidden('#skF_4'(A_187, B_188, C_189), C_189) | k3_xboole_0(A_187, B_188)=C_189)), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_32, plain, (![D_21, B_17, A_16]: (~r2_hidden(D_21, B_17) | ~r2_hidden(D_21, k4_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_73639, plain, (![A_1226, A_1227, B_1228, C_1229]: (~r2_hidden('#skF_3'(A_1226, k4_xboole_0(A_1227, B_1228), C_1229), B_1228) | r2_hidden('#skF_4'(A_1226, k4_xboole_0(A_1227, B_1228), C_1229), C_1229) | k3_xboole_0(A_1226, k4_xboole_0(A_1227, B_1228))=C_1229)), inference(resolution, [status(thm)], [c_1748, c_32])).
% 36.39/24.75  tff(c_73691, plain, (![A_208, A_1227]: (r2_hidden('#skF_4'(A_208, k4_xboole_0(A_1227, A_208), k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_208, k4_xboole_0(A_1227, A_208))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2403, c_73639])).
% 36.39/24.75  tff(c_73732, plain, (![A_1230, A_1231]: (k3_xboole_0(A_1230, k4_xboole_0(A_1231, A_1230))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_381, c_73691])).
% 36.39/24.75  tff(c_956, plain, (![B_145]: (k2_zfmisc_1(k3_xboole_0('#skF_8', B_145), k3_xboole_0('#skF_9', '#skF_11'))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_145), '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_917])).
% 36.39/24.75  tff(c_74477, plain, (![A_1231]: (k2_zfmisc_1(k3_xboole_0('#skF_10', k4_xboole_0(A_1231, '#skF_8')), '#skF_11')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_9', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_73732, c_956])).
% 36.39/24.75  tff(c_74943, plain, (![A_1232]: (k2_zfmisc_1(k3_xboole_0('#skF_10', k4_xboole_0(A_1232, '#skF_8')), '#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74477])).
% 36.39/24.75  tff(c_68, plain, (![B_33, A_32]: (k1_xboole_0=B_33 | k1_xboole_0=A_32 | k2_zfmisc_1(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 36.39/24.75  tff(c_75071, plain, (![A_1232]: (k1_xboole_0='#skF_11' | k3_xboole_0('#skF_10', k4_xboole_0(A_1232, '#skF_8'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74943, c_68])).
% 36.39/24.75  tff(c_77086, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_75071])).
% 36.39/24.75  tff(c_77282, plain, (v1_xboole_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_77086, c_200])).
% 36.39/24.75  tff(c_77289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6198, c_77282])).
% 36.39/24.75  tff(c_77291, plain, (k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_75071])).
% 36.39/24.75  tff(c_34, plain, (![D_21, A_16, B_17]: (r2_hidden(D_21, A_16) | ~r2_hidden(D_21, k4_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_21908, plain, (![A_715, B_716, B_717]: (r2_hidden('#skF_2'(k4_xboole_0(A_715, B_716), B_717), A_715) | r1_tarski(k4_xboole_0(A_715, B_716), B_717))), inference(resolution, [status(thm)], [c_276, c_34])).
% 36.39/24.75  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.39/24.75  tff(c_22016, plain, (![A_718, B_719]: (r1_tarski(k4_xboole_0(A_718, B_719), A_718))), inference(resolution, [status(thm)], [c_21908, c_8])).
% 36.39/24.75  tff(c_64, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.39/24.75  tff(c_22134, plain, (![A_718, B_719]: (k3_xboole_0(k4_xboole_0(A_718, B_719), A_718)=k4_xboole_0(A_718, B_719))), inference(resolution, [status(thm)], [c_22016, c_64])).
% 36.39/24.75  tff(c_1813, plain, (![A_187, B_188]: (r2_hidden('#skF_3'(A_187, B_188, k1_xboole_0), B_188) | k3_xboole_0(A_187, B_188)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1748, c_381])).
% 36.39/24.75  tff(c_92917, plain, (![A_1370, B_1371, B_1372, C_1373]: (~r2_hidden('#skF_3'(k4_xboole_0(A_1370, B_1371), B_1372, C_1373), B_1371) | r2_hidden('#skF_4'(k4_xboole_0(A_1370, B_1371), B_1372, C_1373), C_1373) | k3_xboole_0(k4_xboole_0(A_1370, B_1371), B_1372)=C_1373)), inference(resolution, [status(thm)], [c_2338, c_32])).
% 36.39/24.75  tff(c_92984, plain, (![A_1370, B_188]: (r2_hidden('#skF_4'(k4_xboole_0(A_1370, B_188), B_188, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_1370, B_188), B_188)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1813, c_92917])).
% 36.39/24.75  tff(c_93030, plain, (![A_1374, B_1375]: (k3_xboole_0(k4_xboole_0(A_1374, B_1375), B_1375)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_381, c_92984])).
% 36.39/24.75  tff(c_801, plain, (![A_132, C_133]: (k3_xboole_0(k2_zfmisc_1(A_132, C_133), k2_zfmisc_1('#skF_8', '#skF_9'))=k2_zfmisc_1(k3_xboole_0(A_132, '#skF_10'), k3_xboole_0(C_133, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_766])).
% 36.39/24.75  tff(c_1218, plain, (![A_162, C_163]: (k2_zfmisc_1(k3_xboole_0(A_162, '#skF_10'), k3_xboole_0(C_163, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_162, '#skF_8'), k3_xboole_0(C_163, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_801])).
% 36.39/24.75  tff(c_1257, plain, (![A_162]: (k2_zfmisc_1(k3_xboole_0(A_162, '#skF_8'), k3_xboole_0('#skF_11', '#skF_9'))=k2_zfmisc_1(k3_xboole_0(A_162, '#skF_10'), '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1218])).
% 36.39/24.75  tff(c_93837, plain, (![A_1374]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1374, '#skF_8'), '#skF_10'), '#skF_11')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_11', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_93030, c_1257])).
% 36.39/24.75  tff(c_94348, plain, (![A_1376]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1376, '#skF_8'), '#skF_10'), '#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_93837])).
% 36.39/24.75  tff(c_94424, plain, (k2_zfmisc_1(k4_xboole_0('#skF_10', '#skF_8'), '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22134, c_94348])).
% 36.39/24.75  tff(c_94521, plain, (k1_xboole_0='#skF_11' | k4_xboole_0('#skF_10', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94424, c_68])).
% 36.39/24.75  tff(c_94534, plain, (k4_xboole_0('#skF_10', '#skF_8')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_77291, c_94521])).
% 36.39/24.75  tff(c_693, plain, (![D_122, A_123, B_124]: (r2_hidden(D_122, k4_xboole_0(A_123, B_124)) | r2_hidden(D_122, B_124) | ~r2_hidden(D_122, A_123))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_724, plain, (![A_123, B_124, D_122]: (~v1_xboole_0(k4_xboole_0(A_123, B_124)) | r2_hidden(D_122, B_124) | ~r2_hidden(D_122, A_123))), inference(resolution, [status(thm)], [c_693, c_2])).
% 36.39/24.75  tff(c_94823, plain, (![D_122]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_122, '#skF_8') | ~r2_hidden(D_122, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_94534, c_724])).
% 36.39/24.75  tff(c_95754, plain, (![D_1378]: (r2_hidden(D_1378, '#skF_8') | ~r2_hidden(D_1378, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_94823])).
% 36.39/24.75  tff(c_108244, plain, (![A_1462]: (r2_hidden('#skF_7'(A_1462, '#skF_10'), '#skF_8') | ~r2_xboole_0(A_1462, '#skF_10'))), inference(resolution, [status(thm)], [c_56, c_95754])).
% 36.39/24.75  tff(c_54, plain, (![A_24, B_25]: (~r2_hidden('#skF_7'(A_24, B_25), A_24) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 36.39/24.75  tff(c_108266, plain, (~r2_xboole_0('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_108244, c_54])).
% 36.39/24.75  tff(c_108270, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_48, c_108266])).
% 36.39/24.75  tff(c_108273, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_90, c_108270])).
% 36.39/24.75  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.39/24.75  tff(c_82, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.39/24.75  tff(c_820, plain, (![A_132, C_133]: (k2_zfmisc_1(k3_xboole_0(A_132, '#skF_10'), k3_xboole_0(C_133, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_132, '#skF_8'), k3_xboole_0(C_133, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_801])).
% 36.39/24.75  tff(c_93884, plain, (![A_1374, C_133]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1374, '#skF_10'), '#skF_8'), k3_xboole_0(C_133, '#skF_9'))=k2_zfmisc_1(k1_xboole_0, k3_xboole_0(C_133, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_93030, c_820])).
% 36.39/24.75  tff(c_113951, plain, (![A_1535, C_1536]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_1535, '#skF_10'), '#skF_8'), k3_xboole_0(C_1536, '#skF_9'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_93884])).
% 36.39/24.75  tff(c_114277, plain, (![C_1537]: (k2_zfmisc_1(k4_xboole_0('#skF_8', '#skF_10'), k3_xboole_0(C_1537, '#skF_9'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22134, c_113951])).
% 36.39/24.75  tff(c_114381, plain, (k2_zfmisc_1(k4_xboole_0('#skF_8', '#skF_10'), '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_135, c_114277])).
% 36.39/24.75  tff(c_114421, plain, (k1_xboole_0='#skF_9' | k4_xboole_0('#skF_8', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_114381, c_68])).
% 36.39/24.75  tff(c_114434, plain, (k4_xboole_0('#skF_8', '#skF_10')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_114421])).
% 36.39/24.75  tff(c_114734, plain, (![D_122]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_122, '#skF_10') | ~r2_hidden(D_122, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_114434, c_724])).
% 36.39/24.75  tff(c_114842, plain, (![D_1538]: (r2_hidden(D_1538, '#skF_10') | ~r2_hidden(D_1538, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_114734])).
% 36.39/24.75  tff(c_116133, plain, (![A_1545]: (r1_tarski(A_1545, '#skF_10') | ~r2_hidden('#skF_2'(A_1545, '#skF_10'), '#skF_8'))), inference(resolution, [status(thm)], [c_114842, c_8])).
% 36.39/24.75  tff(c_116157, plain, (r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_10, c_116133])).
% 36.39/24.75  tff(c_116167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108273, c_108273, c_116157])).
% 36.39/24.75  tff(c_116168, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_204])).
% 36.39/24.75  tff(c_116170, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_116168])).
% 36.39/24.75  tff(c_84, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.39/24.75  tff(c_116179, plain, ('#skF_11'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_84])).
% 36.39/24.75  tff(c_116178, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_82])).
% 36.39/24.75  tff(c_116169, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_204])).
% 36.39/24.75  tff(c_116210, plain, (k2_zfmisc_1('#skF_8', '#skF_9')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_116169])).
% 36.39/24.75  tff(c_116412, plain, (![B_1573, A_1574]: (B_1573='#skF_11' | A_1574='#skF_11' | k2_zfmisc_1(A_1574, B_1573)!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_116170, c_116170, c_116170, c_68])).
% 36.39/24.75  tff(c_116421, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_116210, c_116412])).
% 36.39/24.75  tff(c_116429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116179, c_116178, c_116421])).
% 36.39/24.75  tff(c_116430, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_116168])).
% 36.39/24.75  tff(c_116439, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_116430, c_82])).
% 36.39/24.75  tff(c_116468, plain, (k2_zfmisc_1('#skF_8', '#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_116430, c_116169])).
% 36.39/24.75  tff(c_116678, plain, (![B_1602, A_1603]: (B_1602='#skF_10' | A_1603='#skF_10' | k2_zfmisc_1(A_1603, B_1602)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_116430, c_116430, c_116430, c_68])).
% 36.39/24.75  tff(c_116684, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_116468, c_116678])).
% 36.39/24.75  tff(c_116693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_116439, c_116684])).
% 36.39/24.75  tff(c_116694, plain, ('#skF_11'!='#skF_9'), inference(splitRight, [status(thm)], [c_80])).
% 36.39/24.75  tff(c_116956, plain, (![B_1653, A_1654]: (~r2_hidden(B_1653, A_1654) | k4_xboole_0(A_1654, k1_tarski(B_1653))!=A_1654)), inference(cnfTransformation, [status(thm)], [f_99])).
% 36.39/24.75  tff(c_116965, plain, (![B_1653]: (~r2_hidden(B_1653, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_116956])).
% 36.39/24.75  tff(c_118871, plain, (![A_1766, B_1767, C_1768]: (r2_hidden('#skF_3'(A_1766, B_1767, C_1768), B_1767) | r2_hidden('#skF_4'(A_1766, B_1767, C_1768), C_1768) | k3_xboole_0(A_1766, B_1767)=C_1768)), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_118936, plain, (![A_1766, B_1767]: (r2_hidden('#skF_3'(A_1766, B_1767, k1_xboole_0), B_1767) | k3_xboole_0(A_1766, B_1767)=k1_xboole_0)), inference(resolution, [status(thm)], [c_118871, c_116965])).
% 36.39/24.75  tff(c_117864, plain, (![A_1725, B_1726, C_1727]: (r2_hidden('#skF_3'(A_1725, B_1726, C_1727), A_1725) | r2_hidden('#skF_4'(A_1725, B_1726, C_1727), C_1727) | k3_xboole_0(A_1725, B_1726)=C_1727)), inference(cnfTransformation, [status(thm)], [f_47])).
% 36.39/24.75  tff(c_185497, plain, (![A_2774, B_2775, B_2776, C_2777]: (~r2_hidden('#skF_3'(k4_xboole_0(A_2774, B_2775), B_2776, C_2777), B_2775) | r2_hidden('#skF_4'(k4_xboole_0(A_2774, B_2775), B_2776, C_2777), C_2777) | k3_xboole_0(k4_xboole_0(A_2774, B_2775), B_2776)=C_2777)), inference(resolution, [status(thm)], [c_117864, c_32])).
% 36.39/24.75  tff(c_185554, plain, (![A_2774, B_1767]: (r2_hidden('#skF_4'(k4_xboole_0(A_2774, B_1767), B_1767, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_2774, B_1767), B_1767)=k1_xboole_0)), inference(resolution, [status(thm)], [c_118936, c_185497])).
% 36.39/24.75  tff(c_185595, plain, (![A_2778, B_2779]: (k3_xboole_0(k4_xboole_0(A_2778, B_2779), B_2779)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_116965, c_185554])).
% 36.39/24.75  tff(c_116745, plain, (![A_1612, B_1613]: (k3_xboole_0(A_1612, B_1613)=A_1612 | ~r1_tarski(A_1612, B_1613))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.39/24.75  tff(c_116749, plain, (![B_28]: (k3_xboole_0(B_28, B_28)=B_28)), inference(resolution, [status(thm)], [c_62, c_116745])).
% 36.39/24.75  tff(c_116695, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 36.39/24.75  tff(c_116700, plain, (k2_zfmisc_1('#skF_8', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_116695, c_86])).
% 36.39/24.75  tff(c_117397, plain, (![A_1696, C_1697, B_1698, D_1699]: (k3_xboole_0(k2_zfmisc_1(A_1696, C_1697), k2_zfmisc_1(B_1698, D_1699))=k2_zfmisc_1(k3_xboole_0(A_1696, B_1698), k3_xboole_0(C_1697, D_1699)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 36.39/24.75  tff(c_117428, plain, (![A_1696, C_1697]: (k3_xboole_0(k2_zfmisc_1(A_1696, C_1697), k2_zfmisc_1('#skF_8', '#skF_9'))=k2_zfmisc_1(k3_xboole_0(A_1696, '#skF_8'), k3_xboole_0(C_1697, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_116700, c_117397])).
% 36.39/24.75  tff(c_117514, plain, (![A_1701, C_1702]: (k2_zfmisc_1(k3_xboole_0(A_1701, '#skF_8'), k3_xboole_0(C_1702, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_1701, '#skF_8'), k3_xboole_0(C_1702, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117428])).
% 36.39/24.75  tff(c_119027, plain, (![C_1773, A_1774]: (k3_xboole_0(C_1773, '#skF_11')=k1_xboole_0 | k3_xboole_0(A_1774, '#skF_8')=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(A_1774, '#skF_8'), k3_xboole_0(C_1773, '#skF_9'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117514, c_68])).
% 36.39/24.75  tff(c_119078, plain, (![C_1773]: (k3_xboole_0(C_1773, '#skF_11')=k1_xboole_0 | k3_xboole_0('#skF_8', '#skF_8')=k1_xboole_0 | k2_zfmisc_1('#skF_8', k3_xboole_0(C_1773, '#skF_9'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116749, c_119027])).
% 36.39/24.75  tff(c_119102, plain, (![C_1773]: (k3_xboole_0(C_1773, '#skF_11')=k1_xboole_0 | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_8', k3_xboole_0(C_1773, '#skF_9'))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116749, c_119078])).
% 36.39/24.75  tff(c_119103, plain, (![C_1773]: (k3_xboole_0(C_1773, '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_8', k3_xboole_0(C_1773, '#skF_9'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_119102])).
% 36.39/24.75  tff(c_186309, plain, (![A_2778]: (k3_xboole_0(k4_xboole_0(A_2778, '#skF_9'), '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_8', k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185595, c_119103])).
% 36.39/24.75  tff(c_186804, plain, (![A_2780]: (k3_xboole_0(k4_xboole_0(A_2780, '#skF_9'), '#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_186309])).
% 36.39/24.75  tff(c_116934, plain, (![D_1650, A_1651, B_1652]: (r2_hidden(D_1650, A_1651) | ~r2_hidden(D_1650, k4_xboole_0(A_1651, B_1652)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_133124, plain, (![A_2148, B_2149, B_2150]: (r2_hidden('#skF_2'(k4_xboole_0(A_2148, B_2149), B_2150), A_2148) | r1_tarski(k4_xboole_0(A_2148, B_2149), B_2150))), inference(resolution, [status(thm)], [c_10, c_116934])).
% 36.39/24.75  tff(c_133232, plain, (![A_2151, B_2152]: (r1_tarski(k4_xboole_0(A_2151, B_2152), A_2151))), inference(resolution, [status(thm)], [c_133124, c_8])).
% 36.39/24.75  tff(c_133337, plain, (![A_2151, B_2152]: (k3_xboole_0(k4_xboole_0(A_2151, B_2152), A_2151)=k4_xboole_0(A_2151, B_2152))), inference(resolution, [status(thm)], [c_133232, c_64])).
% 36.39/24.75  tff(c_187070, plain, (k4_xboole_0('#skF_11', '#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_186804, c_133337])).
% 36.39/24.75  tff(c_30, plain, (![D_21, A_16, B_17]: (r2_hidden(D_21, k4_xboole_0(A_16, B_17)) | r2_hidden(D_21, B_17) | ~r2_hidden(D_21, A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.39/24.75  tff(c_187737, plain, (![D_21]: (r2_hidden(D_21, k1_xboole_0) | r2_hidden(D_21, '#skF_9') | ~r2_hidden(D_21, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_187070, c_30])).
% 36.39/24.75  tff(c_188049, plain, (![D_2784]: (r2_hidden(D_2784, '#skF_9') | ~r2_hidden(D_2784, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_116965, c_187737])).
% 36.39/24.75  tff(c_195132, plain, (![A_2834]: (r2_hidden('#skF_7'(A_2834, '#skF_11'), '#skF_9') | ~r2_xboole_0(A_2834, '#skF_11'))), inference(resolution, [status(thm)], [c_56, c_188049])).
% 36.39/24.75  tff(c_195151, plain, (~r2_xboole_0('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_195132, c_54])).
% 36.39/24.75  tff(c_195155, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_48, c_195151])).
% 36.39/24.75  tff(c_195158, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_116694, c_195155])).
% 36.39/24.75  tff(c_117541, plain, (![C_1702]: (k2_zfmisc_1(k3_xboole_0('#skF_8', '#skF_8'), k3_xboole_0(C_1702, '#skF_9'))=k2_zfmisc_1('#skF_8', k3_xboole_0(C_1702, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_116749, c_117514])).
% 36.39/24.75  tff(c_117552, plain, (![C_1702]: (k2_zfmisc_1('#skF_8', k3_xboole_0(C_1702, '#skF_11'))=k2_zfmisc_1('#skF_8', k3_xboole_0(C_1702, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_116749, c_117541])).
% 36.39/24.75  tff(c_186281, plain, (![A_2778]: (k2_zfmisc_1('#skF_8', k3_xboole_0(k4_xboole_0(A_2778, '#skF_11'), '#skF_9'))=k2_zfmisc_1('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_185595, c_117552])).
% 36.39/24.75  tff(c_190821, plain, (![A_2812]: (k2_zfmisc_1('#skF_8', k3_xboole_0(k4_xboole_0(A_2812, '#skF_11'), '#skF_9'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_186281])).
% 36.39/24.75  tff(c_190850, plain, (![A_2812]: (k3_xboole_0(k4_xboole_0(A_2812, '#skF_11'), '#skF_9')=k1_xboole_0 | k1_xboole_0='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_190821, c_68])).
% 36.39/24.75  tff(c_190989, plain, (![A_2813]: (k3_xboole_0(k4_xboole_0(A_2813, '#skF_11'), '#skF_9')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_84, c_190850])).
% 36.39/24.75  tff(c_191283, plain, (k4_xboole_0('#skF_9', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_190989, c_133337])).
% 36.39/24.75  tff(c_192057, plain, (![D_21]: (r2_hidden(D_21, k1_xboole_0) | r2_hidden(D_21, '#skF_11') | ~r2_hidden(D_21, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_191283, c_30])).
% 36.39/24.75  tff(c_192187, plain, (![D_2814]: (r2_hidden(D_2814, '#skF_11') | ~r2_hidden(D_2814, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_116965, c_192057])).
% 36.39/24.75  tff(c_196247, plain, (![A_2842]: (r1_tarski(A_2842, '#skF_11') | ~r2_hidden('#skF_2'(A_2842, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_192187, c_8])).
% 36.39/24.75  tff(c_196271, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_10, c_196247])).
% 36.39/24.75  tff(c_196281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195158, c_195158, c_196271])).
% 36.39/24.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.39/24.75  
% 36.39/24.75  Inference rules
% 36.39/24.75  ----------------------
% 36.39/24.75  #Ref     : 0
% 36.39/24.75  #Sup     : 50310
% 36.39/24.75  #Fact    : 0
% 36.39/24.75  #Define  : 0
% 36.39/24.75  #Split   : 23
% 36.39/24.75  #Chain   : 0
% 36.39/24.75  #Close   : 0
% 36.39/24.75  
% 36.39/24.75  Ordering : KBO
% 36.39/24.75  
% 36.39/24.75  Simplification rules
% 36.39/24.75  ----------------------
% 36.39/24.75  #Subsume      : 17535
% 36.39/24.75  #Demod        : 32667
% 36.39/24.75  #Tautology    : 16482
% 36.39/24.75  #SimpNegUnit  : 939
% 36.39/24.75  #BackRed      : 925
% 36.39/24.75  
% 36.39/24.75  #Partial instantiations: 0
% 36.39/24.75  #Strategies tried      : 1
% 36.39/24.75  
% 36.39/24.75  Timing (in seconds)
% 36.39/24.75  ----------------------
% 36.39/24.76  Preprocessing        : 0.32
% 36.39/24.76  Parsing              : 0.16
% 36.39/24.76  CNF conversion       : 0.03
% 36.39/24.76  Main loop            : 23.63
% 36.39/24.76  Inferencing          : 3.79
% 36.39/24.76  Reduction            : 6.96
% 36.39/24.76  Demodulation         : 5.13
% 36.39/24.76  BG Simplification    : 0.41
% 36.39/24.76  Subsumption          : 11.03
% 36.39/24.76  Abstraction          : 0.65
% 36.39/24.76  MUC search           : 0.00
% 36.39/24.76  Cooper               : 0.00
% 36.39/24.76  Total                : 24.02
% 36.39/24.76  Index Insertion      : 0.00
% 36.39/24.76  Index Deletion       : 0.00
% 36.39/24.76  Index Matching       : 0.00
% 36.39/24.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
