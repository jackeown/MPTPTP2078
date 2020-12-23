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
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 173 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 322 expanded)
%              Number of equality atoms :   69 ( 244 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_177,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),B_58)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_406,plain,(
    ! [B_76,A_77] :
      ( r1_xboole_0(B_76,k1_tarski(A_77))
      | r2_hidden(A_77,B_76) ) ),
    inference(resolution,[status(thm)],[c_177,c_2])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1460,plain,(
    ! [B_145,A_146] :
      ( k4_xboole_0(B_145,k1_tarski(A_146)) = B_145
      | r2_hidden(A_146,B_145) ) ),
    inference(resolution,[status(thm)],[c_406,c_16])).

tff(c_56,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_152,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(A_53,B_54)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_1477,plain,
    ( k1_xboole_0 = '#skF_2'
    | r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_159])).

tff(c_1498,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1477])).

tff(c_22,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1110,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k2_tarski(A_122,B_123),C_124)
      | ~ r2_hidden(B_123,C_124)
      | ~ r2_hidden(A_122,C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2847,plain,(
    ! [A_182,C_183] :
      ( r1_tarski(k1_tarski(A_182),C_183)
      | ~ r2_hidden(A_182,C_183)
      | ~ r2_hidden(A_182,C_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1110])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2861,plain,(
    ! [A_184,C_185] :
      ( k2_xboole_0(k1_tarski(A_184),C_185) = C_185
      | ~ r2_hidden(A_184,C_185) ) ),
    inference(resolution,[status(thm)],[c_2847,c_6])).

tff(c_63,plain,(
    ! [A_39,B_40] : r1_tarski(A_39,k2_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_63])).

tff(c_181,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_181])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_278,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_414,plain,(
    ! [B_78,A_79] : k3_tarski(k2_tarski(B_78,A_79)) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_278])).

tff(c_42,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_420,plain,(
    ! [B_78,A_79] : k2_xboole_0(B_78,A_79) = k2_xboole_0(A_79,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_42])).

tff(c_475,plain,(
    ! [B_83,A_84] : k2_xboole_0(B_83,A_84) = k2_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_42])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_800,plain,(
    ! [A_102,B_103] : r1_tarski(A_102,k2_xboole_0(B_103,A_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_14])).

tff(c_2141,plain,(
    ! [A_168,B_169] : k2_xboole_0(A_168,k2_xboole_0(B_169,A_168)) = k2_xboole_0(B_169,A_168) ),
    inference(resolution,[status(thm)],[c_800,c_6])).

tff(c_2427,plain,(
    ! [A_174,B_175] : k2_xboole_0(A_174,k2_xboole_0(A_174,B_175)) = k2_xboole_0(B_175,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_2141])).

tff(c_2554,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2427])).

tff(c_2601,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_2554])).

tff(c_2871,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2861,c_2601])).

tff(c_3020,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_2871])).

tff(c_3022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3020])).

tff(c_3023,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3024,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3025,plain,(
    ! [A_9] : r1_tarski('#skF_2',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_10])).

tff(c_3145,plain,(
    ! [A_205,B_206] :
      ( k2_xboole_0(A_205,B_206) = B_206
      | ~ r1_tarski(A_205,B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3164,plain,(
    ! [A_9] : k2_xboole_0('#skF_2',A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_3025,c_3145])).

tff(c_3166,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3164,c_56])).

tff(c_3168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3023,c_3166])).

tff(c_3170,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3260,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_3170,c_54])).

tff(c_3169,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3172,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_56])).

tff(c_3368,plain,(
    ! [A_229,B_230] :
      ( r1_xboole_0(k1_tarski(A_229),B_230)
      | r2_hidden(A_229,B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4811,plain,(
    ! [B_309,A_310] :
      ( r1_xboole_0(B_309,k1_tarski(A_310))
      | r2_hidden(A_310,B_309) ) ),
    inference(resolution,[status(thm)],[c_3368,c_2])).

tff(c_5257,plain,(
    ! [B_330,A_331] :
      ( k4_xboole_0(B_330,k1_tarski(A_331)) = B_330
      | r2_hidden(A_331,B_330) ) ),
    inference(resolution,[status(thm)],[c_4811,c_16])).

tff(c_5284,plain,(
    ! [B_330] :
      ( k4_xboole_0(B_330,'#skF_2') = B_330
      | r2_hidden('#skF_1',B_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3170,c_5257])).

tff(c_4529,plain,(
    ! [A_289,B_290,C_291] :
      ( r1_tarski(k2_tarski(A_289,B_290),C_291)
      | ~ r2_hidden(B_290,C_291)
      | ~ r2_hidden(A_289,C_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7630,plain,(
    ! [A_374,C_375] :
      ( r1_tarski(k1_tarski(A_374),C_375)
      | ~ r2_hidden(A_374,C_375)
      | ~ r2_hidden(A_374,C_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4529])).

tff(c_7647,plain,(
    ! [A_376,C_377] :
      ( k2_xboole_0(k1_tarski(A_376),C_377) = C_377
      | ~ r2_hidden(A_376,C_377) ) ),
    inference(resolution,[status(thm)],[c_7630,c_6])).

tff(c_7910,plain,(
    ! [C_379] :
      ( k2_xboole_0('#skF_2',C_379) = C_379
      | ~ r2_hidden('#skF_1',C_379) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3170,c_7647])).

tff(c_8861,plain,(
    ! [B_405] :
      ( k2_xboole_0('#skF_2',B_405) = B_405
      | k4_xboole_0(B_405,'#skF_2') = B_405 ) ),
    inference(resolution,[status(thm)],[c_5284,c_7910])).

tff(c_3592,plain,(
    ! [A_243,B_244] : k3_tarski(k2_tarski(A_243,B_244)) = k2_xboole_0(A_243,B_244) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3920,plain,(
    ! [A_262,B_263] : k3_tarski(k2_tarski(A_262,B_263)) = k2_xboole_0(B_263,A_262) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3592])).

tff(c_3946,plain,(
    ! [B_264,A_265] : k2_xboole_0(B_264,A_265) = k2_xboole_0(A_265,B_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_3920,c_42])).

tff(c_4014,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3172,c_3946])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4120,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4014,c_12])).

tff(c_8877,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8861,c_4120])).

tff(c_8905,plain,
    ( k1_xboole_0 = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_8877])).

tff(c_8907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3260,c_3169,c_8905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.29  
% 6.00/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.00/2.29  
% 6.00/2.29  %Foreground sorts:
% 6.00/2.29  
% 6.00/2.29  
% 6.00/2.29  %Background operators:
% 6.00/2.29  
% 6.00/2.29  
% 6.00/2.29  %Foreground operators:
% 6.00/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.00/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.00/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.00/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.00/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.00/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.00/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.00/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.00/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.00/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.00/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.00/2.29  
% 6.08/2.31  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.08/2.31  tff(f_62, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.08/2.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.08/2.31  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.08/2.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.08/2.31  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.08/2.31  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.08/2.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.08/2.31  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.08/2.31  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.08/2.31  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.08/2.31  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.08/2.31  tff(c_50, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.31  tff(c_67, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 6.08/2.31  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.31  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 6.08/2.31  tff(c_177, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), B_58) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.08/2.31  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.08/2.31  tff(c_406, plain, (![B_76, A_77]: (r1_xboole_0(B_76, k1_tarski(A_77)) | r2_hidden(A_77, B_76))), inference(resolution, [status(thm)], [c_177, c_2])).
% 6.08/2.31  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.08/2.31  tff(c_1460, plain, (![B_145, A_146]: (k4_xboole_0(B_145, k1_tarski(A_146))=B_145 | r2_hidden(A_146, B_145))), inference(resolution, [status(thm)], [c_406, c_16])).
% 6.08/2.31  tff(c_56, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.31  tff(c_152, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(A_53, B_54))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.08/2.31  tff(c_159, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_56, c_152])).
% 6.08/2.31  tff(c_1477, plain, (k1_xboole_0='#skF_2' | r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1460, c_159])).
% 6.08/2.31  tff(c_1498, plain, (r2_hidden('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_1477])).
% 6.08/2.31  tff(c_22, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.08/2.31  tff(c_1110, plain, (![A_122, B_123, C_124]: (r1_tarski(k2_tarski(A_122, B_123), C_124) | ~r2_hidden(B_123, C_124) | ~r2_hidden(A_122, C_124))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.08/2.31  tff(c_2847, plain, (![A_182, C_183]: (r1_tarski(k1_tarski(A_182), C_183) | ~r2_hidden(A_182, C_183) | ~r2_hidden(A_182, C_183))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1110])).
% 6.08/2.31  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.08/2.31  tff(c_2861, plain, (![A_184, C_185]: (k2_xboole_0(k1_tarski(A_184), C_185)=C_185 | ~r2_hidden(A_184, C_185))), inference(resolution, [status(thm)], [c_2847, c_6])).
% 6.08/2.31  tff(c_63, plain, (![A_39, B_40]: (r1_tarski(A_39, k2_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.31  tff(c_66, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_63])).
% 6.08/2.31  tff(c_181, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.08/2.31  tff(c_203, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_66, c_181])).
% 6.08/2.31  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.08/2.31  tff(c_278, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.31  tff(c_414, plain, (![B_78, A_79]: (k3_tarski(k2_tarski(B_78, A_79))=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_20, c_278])).
% 6.08/2.31  tff(c_42, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.31  tff(c_420, plain, (![B_78, A_79]: (k2_xboole_0(B_78, A_79)=k2_xboole_0(A_79, B_78))), inference(superposition, [status(thm), theory('equality')], [c_414, c_42])).
% 6.08/2.31  tff(c_475, plain, (![B_83, A_84]: (k2_xboole_0(B_83, A_84)=k2_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_414, c_42])).
% 6.08/2.31  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.31  tff(c_800, plain, (![A_102, B_103]: (r1_tarski(A_102, k2_xboole_0(B_103, A_102)))), inference(superposition, [status(thm), theory('equality')], [c_475, c_14])).
% 6.08/2.31  tff(c_2141, plain, (![A_168, B_169]: (k2_xboole_0(A_168, k2_xboole_0(B_169, A_168))=k2_xboole_0(B_169, A_168))), inference(resolution, [status(thm)], [c_800, c_6])).
% 6.08/2.31  tff(c_2427, plain, (![A_174, B_175]: (k2_xboole_0(A_174, k2_xboole_0(A_174, B_175))=k2_xboole_0(B_175, A_174))), inference(superposition, [status(thm), theory('equality')], [c_420, c_2141])).
% 6.08/2.31  tff(c_2554, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_2427])).
% 6.08/2.31  tff(c_2601, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_2554])).
% 6.08/2.31  tff(c_2871, plain, (k1_tarski('#skF_1')='#skF_2' | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2861, c_2601])).
% 6.08/2.31  tff(c_3020, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_2871])).
% 6.08/2.31  tff(c_3022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_3020])).
% 6.08/2.31  tff(c_3023, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 6.08/2.31  tff(c_3024, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 6.08/2.31  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.08/2.31  tff(c_3025, plain, (![A_9]: (r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_3024, c_10])).
% 6.08/2.31  tff(c_3145, plain, (![A_205, B_206]: (k2_xboole_0(A_205, B_206)=B_206 | ~r1_tarski(A_205, B_206))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.08/2.31  tff(c_3164, plain, (![A_9]: (k2_xboole_0('#skF_2', A_9)=A_9)), inference(resolution, [status(thm)], [c_3025, c_3145])).
% 6.08/2.31  tff(c_3166, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3164, c_56])).
% 6.08/2.31  tff(c_3168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3023, c_3166])).
% 6.08/2.31  tff(c_3170, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 6.08/2.31  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.31  tff(c_3260, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3170, c_3170, c_54])).
% 6.08/2.31  tff(c_3169, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 6.08/2.31  tff(c_3172, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3170, c_56])).
% 6.08/2.31  tff(c_3368, plain, (![A_229, B_230]: (r1_xboole_0(k1_tarski(A_229), B_230) | r2_hidden(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.08/2.31  tff(c_4811, plain, (![B_309, A_310]: (r1_xboole_0(B_309, k1_tarski(A_310)) | r2_hidden(A_310, B_309))), inference(resolution, [status(thm)], [c_3368, c_2])).
% 6.08/2.31  tff(c_5257, plain, (![B_330, A_331]: (k4_xboole_0(B_330, k1_tarski(A_331))=B_330 | r2_hidden(A_331, B_330))), inference(resolution, [status(thm)], [c_4811, c_16])).
% 6.08/2.31  tff(c_5284, plain, (![B_330]: (k4_xboole_0(B_330, '#skF_2')=B_330 | r2_hidden('#skF_1', B_330))), inference(superposition, [status(thm), theory('equality')], [c_3170, c_5257])).
% 6.08/2.31  tff(c_4529, plain, (![A_289, B_290, C_291]: (r1_tarski(k2_tarski(A_289, B_290), C_291) | ~r2_hidden(B_290, C_291) | ~r2_hidden(A_289, C_291))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.08/2.31  tff(c_7630, plain, (![A_374, C_375]: (r1_tarski(k1_tarski(A_374), C_375) | ~r2_hidden(A_374, C_375) | ~r2_hidden(A_374, C_375))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4529])).
% 6.08/2.31  tff(c_7647, plain, (![A_376, C_377]: (k2_xboole_0(k1_tarski(A_376), C_377)=C_377 | ~r2_hidden(A_376, C_377))), inference(resolution, [status(thm)], [c_7630, c_6])).
% 6.08/2.31  tff(c_7910, plain, (![C_379]: (k2_xboole_0('#skF_2', C_379)=C_379 | ~r2_hidden('#skF_1', C_379))), inference(superposition, [status(thm), theory('equality')], [c_3170, c_7647])).
% 6.08/2.31  tff(c_8861, plain, (![B_405]: (k2_xboole_0('#skF_2', B_405)=B_405 | k4_xboole_0(B_405, '#skF_2')=B_405)), inference(resolution, [status(thm)], [c_5284, c_7910])).
% 6.08/2.31  tff(c_3592, plain, (![A_243, B_244]: (k3_tarski(k2_tarski(A_243, B_244))=k2_xboole_0(A_243, B_244))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.31  tff(c_3920, plain, (![A_262, B_263]: (k3_tarski(k2_tarski(A_262, B_263))=k2_xboole_0(B_263, A_262))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3592])).
% 6.08/2.31  tff(c_3946, plain, (![B_264, A_265]: (k2_xboole_0(B_264, A_265)=k2_xboole_0(A_265, B_264))), inference(superposition, [status(thm), theory('equality')], [c_3920, c_42])).
% 6.08/2.31  tff(c_4014, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3172, c_3946])).
% 6.08/2.31  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.08/2.31  tff(c_4120, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4014, c_12])).
% 6.08/2.31  tff(c_8877, plain, (k1_xboole_0='#skF_3' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8861, c_4120])).
% 6.08/2.31  tff(c_8905, plain, (k1_xboole_0='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_8877])).
% 6.08/2.31  tff(c_8907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3260, c_3169, c_8905])).
% 6.08/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.31  
% 6.08/2.31  Inference rules
% 6.08/2.31  ----------------------
% 6.08/2.31  #Ref     : 0
% 6.08/2.31  #Sup     : 2114
% 6.08/2.31  #Fact    : 0
% 6.08/2.31  #Define  : 0
% 6.08/2.31  #Split   : 5
% 6.08/2.31  #Chain   : 0
% 6.08/2.31  #Close   : 0
% 6.08/2.31  
% 6.08/2.31  Ordering : KBO
% 6.08/2.31  
% 6.08/2.31  Simplification rules
% 6.08/2.31  ----------------------
% 6.08/2.31  #Subsume      : 118
% 6.08/2.31  #Demod        : 1963
% 6.08/2.31  #Tautology    : 1629
% 6.08/2.31  #SimpNegUnit  : 25
% 6.08/2.31  #BackRed      : 17
% 6.08/2.31  
% 6.08/2.31  #Partial instantiations: 0
% 6.08/2.31  #Strategies tried      : 1
% 6.08/2.31  
% 6.08/2.31  Timing (in seconds)
% 6.08/2.31  ----------------------
% 6.08/2.31  Preprocessing        : 0.33
% 6.08/2.31  Parsing              : 0.18
% 6.08/2.31  CNF conversion       : 0.02
% 6.08/2.31  Main loop            : 1.19
% 6.08/2.31  Inferencing          : 0.38
% 6.08/2.31  Reduction            : 0.53
% 6.08/2.31  Demodulation         : 0.44
% 6.08/2.31  BG Simplification    : 0.04
% 6.08/2.31  Subsumption          : 0.16
% 6.08/2.31  Abstraction          : 0.05
% 6.08/2.31  MUC search           : 0.00
% 6.08/2.31  Cooper               : 0.00
% 6.08/2.31  Total                : 1.56
% 6.08/2.31  Index Insertion      : 0.00
% 6.08/2.31  Index Deletion       : 0.00
% 6.08/2.31  Index Matching       : 0.00
% 6.08/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
