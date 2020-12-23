%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 13.27s
% Output     : CNFRefutation 13.27s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 260 expanded)
%              Number of leaves         :   35 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  129 ( 353 expanded)
%              Number of equality atoms :   61 ( 180 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_76,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3045,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden('#skF_2'(A_178,B_179,C_180),A_178)
      | r2_hidden('#skF_3'(A_178,B_179,C_180),C_180)
      | k3_xboole_0(A_178,B_179) = C_180 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_2'(A_10,B_11,C_12),C_12)
      | r2_hidden('#skF_3'(A_10,B_11,C_12),C_12)
      | k3_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3096,plain,(
    ! [A_178,B_179] :
      ( r2_hidden('#skF_3'(A_178,B_179,A_178),A_178)
      | k3_xboole_0(A_178,B_179) = A_178 ) ),
    inference(resolution,[status(thm)],[c_3045,c_24])).

tff(c_46,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_277,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | ~ r1_tarski(k1_tarski(A_62),B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_282,plain,(
    ! [A_62] : r2_hidden(A_62,k1_tarski(A_62)) ),
    inference(resolution,[status(thm)],[c_46,c_277])).

tff(c_284,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tarski(A_65),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1094,plain,(
    ! [A_124,B_125] :
      ( k3_xboole_0(k1_tarski(A_124),B_125) = k1_tarski(A_124)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_284,c_52])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1122,plain,(
    ! [B_125,A_124] :
      ( k3_xboole_0(B_125,k1_tarski(A_124)) = k1_tarski(A_124)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_4])).

tff(c_364,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4297,plain,(
    ! [A_220,B_221,B_222] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_220,B_221),B_222),B_221)
      | r1_tarski(k3_xboole_0(A_220,B_221),B_222) ) ),
    inference(resolution,[status(thm)],[c_364,c_14])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4349,plain,(
    ! [A_223,B_224] : r1_tarski(k3_xboole_0(A_223,B_224),B_224) ),
    inference(resolution,[status(thm)],[c_4297,c_8])).

tff(c_4435,plain,(
    ! [A_228,B_229] : k3_xboole_0(k3_xboole_0(A_228,B_229),B_229) = k3_xboole_0(A_228,B_229) ),
    inference(resolution,[status(thm)],[c_4349,c_52])).

tff(c_4917,plain,(
    ! [B_239,A_240] : k3_xboole_0(k3_xboole_0(B_239,A_240),B_239) = k3_xboole_0(A_240,B_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4435])).

tff(c_4372,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4349])).

tff(c_5062,plain,(
    ! [A_241,B_242] : r1_tarski(k3_xboole_0(A_241,B_242),k3_xboole_0(B_242,A_241)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4917,c_4372])).

tff(c_14807,plain,(
    ! [A_418,B_419] :
      ( r1_tarski(k1_tarski(A_418),k3_xboole_0(k1_tarski(A_418),B_419))
      | ~ r2_hidden(A_418,B_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_5062])).

tff(c_68,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r1_tarski(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14879,plain,(
    ! [A_418,B_419] :
      ( r2_hidden(A_418,k3_xboole_0(k1_tarski(A_418),B_419))
      | ~ r2_hidden(A_418,B_419) ) ),
    inference(resolution,[status(thm)],[c_14807,c_68])).

tff(c_56,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_782,plain,(
    ! [A_104,C_105,B_106] :
      ( ~ r2_hidden(A_104,C_105)
      | ~ r2_hidden(A_104,B_106)
      | ~ r2_hidden(A_104,k5_xboole_0(B_106,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6182,plain,(
    ! [A_260,A_261,B_262] :
      ( ~ r2_hidden(A_260,k3_xboole_0(A_261,B_262))
      | ~ r2_hidden(A_260,A_261)
      | ~ r2_hidden(A_260,k4_xboole_0(A_261,B_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_782])).

tff(c_21987,plain,(
    ! [A_568,A_569] :
      ( ~ r2_hidden(A_568,k3_xboole_0(A_569,k1_xboole_0))
      | ~ r2_hidden(A_568,A_569)
      | ~ r2_hidden(A_568,A_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_6182])).

tff(c_22087,plain,(
    ! [A_418] :
      ( ~ r2_hidden(A_418,k1_tarski(A_418))
      | ~ r2_hidden(A_418,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14879,c_21987])).

tff(c_22308,plain,(
    ! [A_570] : ~ r2_hidden(A_570,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_22087])).

tff(c_22498,plain,(
    ! [B_179] : k3_xboole_0(k1_xboole_0,B_179) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3096,c_22308])).

tff(c_293,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_308,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_293])).

tff(c_4473,plain,(
    ! [B_229,A_228] : k5_xboole_0(B_229,k3_xboole_0(A_228,B_229)) = k4_xboole_0(B_229,k3_xboole_0(A_228,B_229)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_308])).

tff(c_4527,plain,(
    ! [B_229,A_228] : k4_xboole_0(B_229,k3_xboole_0(A_228,B_229)) = k4_xboole_0(B_229,A_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_4473])).

tff(c_140,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_156,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_50])).

tff(c_376,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),B_82) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_418,plain,(
    ! [A_83] : k4_xboole_0(k1_xboole_0,A_83) = k4_xboole_0(A_83,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_376])).

tff(c_54,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_430,plain,(
    ! [A_83] : k2_xboole_0(A_83,k4_xboole_0(A_83,A_83)) = k2_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_54])).

tff(c_457,plain,(
    ! [A_87] : k2_xboole_0(A_87,k4_xboole_0(A_87,A_87)) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_430])).

tff(c_466,plain,(
    ! [A_87] : k2_xboole_0(A_87,A_87) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_54])).

tff(c_398,plain,(
    ! [A_52] : k4_xboole_0(k1_xboole_0,A_52) = k4_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_376])).

tff(c_4751,plain,(
    ! [B_234,A_235] : k3_xboole_0(B_234,k3_xboole_0(A_235,B_234)) = k3_xboole_0(A_235,B_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_4])).

tff(c_4760,plain,(
    ! [A_235,B_234] : k4_xboole_0(k3_xboole_0(A_235,B_234),k3_xboole_0(A_235,B_234)) = k4_xboole_0(k3_xboole_0(A_235,B_234),B_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_4751,c_4527])).

tff(c_8732,plain,(
    ! [A_319,B_320] : k4_xboole_0(k3_xboole_0(A_319,B_320),B_320) = k4_xboole_0(k1_xboole_0,k3_xboole_0(A_319,B_320)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_4760])).

tff(c_8906,plain,(
    ! [A_323] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_323,k1_xboole_0)) = k3_xboole_0(A_323,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8732,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5338,plain,(
    ! [A_247,B_248] : k4_xboole_0(k2_xboole_0(A_247,B_248),k4_xboole_0(B_248,A_247)) = k4_xboole_0(A_247,k4_xboole_0(B_248,A_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_376])).

tff(c_5464,plain,(
    ! [A_52] : k4_xboole_0(k2_xboole_0(A_52,k1_xboole_0),k4_xboole_0(A_52,A_52)) = k4_xboole_0(A_52,k4_xboole_0(k1_xboole_0,A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_5338])).

tff(c_6950,plain,(
    ! [A_289] : k4_xboole_0(A_289,k4_xboole_0(k1_xboole_0,A_289)) = k4_xboole_0(A_289,k4_xboole_0(A_289,A_289)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5464])).

tff(c_7061,plain,(
    ! [A_289] : k2_xboole_0(k4_xboole_0(k1_xboole_0,A_289),k4_xboole_0(A_289,k4_xboole_0(A_289,A_289))) = k2_xboole_0(k4_xboole_0(k1_xboole_0,A_289),A_289) ),
    inference(superposition,[status(thm),theory(equality)],[c_6950,c_54])).

tff(c_7224,plain,(
    ! [A_293] : k2_xboole_0(k4_xboole_0(k1_xboole_0,A_293),k4_xboole_0(A_293,k4_xboole_0(A_293,A_293))) = A_293 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54,c_2,c_7061])).

tff(c_7315,plain,(
    ! [A_52] : k2_xboole_0(k4_xboole_0(k1_xboole_0,A_52),k4_xboole_0(A_52,k4_xboole_0(k1_xboole_0,A_52))) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_7224])).

tff(c_8918,plain,(
    ! [A_323] : k2_xboole_0(k4_xboole_0(k1_xboole_0,k3_xboole_0(A_323,k1_xboole_0)),k4_xboole_0(k3_xboole_0(A_323,k1_xboole_0),k3_xboole_0(A_323,k1_xboole_0))) = k3_xboole_0(A_323,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8906,c_7315])).

tff(c_9062,plain,(
    ! [A_323] : k4_xboole_0(k1_xboole_0,A_323) = k3_xboole_0(A_323,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4527,c_466,c_398,c_8918])).

tff(c_263,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_267,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_46,c_263])).

tff(c_302,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k4_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_293])).

tff(c_1115,plain,(
    ! [A_124,B_125] :
      ( k5_xboole_0(k1_tarski(A_124),k1_tarski(A_124)) = k4_xboole_0(k1_tarski(A_124),B_125)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_48])).

tff(c_1142,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(k1_tarski(A_124),B_125) = k4_xboole_0(k1_xboole_0,k1_tarski(A_124))
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_302,c_1115])).

tff(c_21641,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(k1_tarski(A_124),B_125) = k3_xboole_0(k1_xboole_0,k1_tarski(A_124))
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_9062,c_1142])).

tff(c_26195,plain,(
    ! [A_654,B_655] :
      ( k4_xboole_0(k1_tarski(A_654),B_655) = k1_xboole_0
      | ~ r2_hidden(A_654,B_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22498,c_21641])).

tff(c_26288,plain,(
    ! [B_655,A_654] :
      ( k2_xboole_0(B_655,k1_tarski(A_654)) = k2_xboole_0(B_655,k1_xboole_0)
      | ~ r2_hidden(A_654,B_655) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26195,c_54])).

tff(c_26918,plain,(
    ! [B_662,A_663] :
      ( k2_xboole_0(B_662,k1_tarski(A_663)) = B_662
      | ~ r2_hidden(A_663,B_662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26288])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_78,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_27001,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26918,c_78])).

tff(c_27044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_27001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.27/5.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.27/5.60  
% 13.27/5.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.27/5.60  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 13.27/5.60  
% 13.27/5.60  %Foreground sorts:
% 13.27/5.60  
% 13.27/5.60  
% 13.27/5.60  %Background operators:
% 13.27/5.60  
% 13.27/5.60  
% 13.27/5.60  %Foreground operators:
% 13.27/5.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.27/5.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.27/5.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.27/5.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.27/5.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.27/5.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.27/5.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.27/5.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.27/5.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.27/5.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.27/5.60  tff('#skF_5', type, '#skF_5': $i).
% 13.27/5.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.27/5.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.27/5.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.27/5.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.27/5.60  tff('#skF_4', type, '#skF_4': $i).
% 13.27/5.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.27/5.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.27/5.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.27/5.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.27/5.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.27/5.60  
% 13.27/5.62  tff(f_91, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 13.27/5.62  tff(f_62, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.27/5.62  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.27/5.62  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.27/5.62  tff(f_84, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 13.27/5.62  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.27/5.62  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.27/5.62  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.27/5.62  tff(f_70, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.27/5.62  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.27/5.62  tff(f_52, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 13.27/5.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.27/5.62  tff(f_72, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 13.27/5.62  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.27/5.62  tff(c_76, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.27/5.62  tff(c_50, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.27/5.62  tff(c_3045, plain, (![A_178, B_179, C_180]: (r2_hidden('#skF_2'(A_178, B_179, C_180), A_178) | r2_hidden('#skF_3'(A_178, B_179, C_180), C_180) | k3_xboole_0(A_178, B_179)=C_180)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.27/5.62  tff(c_24, plain, (![A_10, B_11, C_12]: (~r2_hidden('#skF_2'(A_10, B_11, C_12), C_12) | r2_hidden('#skF_3'(A_10, B_11, C_12), C_12) | k3_xboole_0(A_10, B_11)=C_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.27/5.62  tff(c_3096, plain, (![A_178, B_179]: (r2_hidden('#skF_3'(A_178, B_179, A_178), A_178) | k3_xboole_0(A_178, B_179)=A_178)), inference(resolution, [status(thm)], [c_3045, c_24])).
% 13.27/5.62  tff(c_46, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.27/5.62  tff(c_277, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | ~r1_tarski(k1_tarski(A_62), B_63))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.27/5.62  tff(c_282, plain, (![A_62]: (r2_hidden(A_62, k1_tarski(A_62)))), inference(resolution, [status(thm)], [c_46, c_277])).
% 13.27/5.62  tff(c_284, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.27/5.62  tff(c_52, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.27/5.62  tff(c_1094, plain, (![A_124, B_125]: (k3_xboole_0(k1_tarski(A_124), B_125)=k1_tarski(A_124) | ~r2_hidden(A_124, B_125))), inference(resolution, [status(thm)], [c_284, c_52])).
% 13.27/5.62  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.27/5.62  tff(c_1122, plain, (![B_125, A_124]: (k3_xboole_0(B_125, k1_tarski(A_124))=k1_tarski(A_124) | ~r2_hidden(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_4])).
% 13.27/5.62  tff(c_364, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), A_79) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.27/5.62  tff(c_14, plain, (![D_15, B_11, A_10]: (r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.27/5.62  tff(c_4297, plain, (![A_220, B_221, B_222]: (r2_hidden('#skF_1'(k3_xboole_0(A_220, B_221), B_222), B_221) | r1_tarski(k3_xboole_0(A_220, B_221), B_222))), inference(resolution, [status(thm)], [c_364, c_14])).
% 13.27/5.62  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.27/5.62  tff(c_4349, plain, (![A_223, B_224]: (r1_tarski(k3_xboole_0(A_223, B_224), B_224))), inference(resolution, [status(thm)], [c_4297, c_8])).
% 13.27/5.62  tff(c_4435, plain, (![A_228, B_229]: (k3_xboole_0(k3_xboole_0(A_228, B_229), B_229)=k3_xboole_0(A_228, B_229))), inference(resolution, [status(thm)], [c_4349, c_52])).
% 13.27/5.62  tff(c_4917, plain, (![B_239, A_240]: (k3_xboole_0(k3_xboole_0(B_239, A_240), B_239)=k3_xboole_0(A_240, B_239))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4435])).
% 13.27/5.62  tff(c_4372, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4349])).
% 13.27/5.62  tff(c_5062, plain, (![A_241, B_242]: (r1_tarski(k3_xboole_0(A_241, B_242), k3_xboole_0(B_242, A_241)))), inference(superposition, [status(thm), theory('equality')], [c_4917, c_4372])).
% 13.27/5.62  tff(c_14807, plain, (![A_418, B_419]: (r1_tarski(k1_tarski(A_418), k3_xboole_0(k1_tarski(A_418), B_419)) | ~r2_hidden(A_418, B_419))), inference(superposition, [status(thm), theory('equality')], [c_1122, c_5062])).
% 13.27/5.62  tff(c_68, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r1_tarski(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.27/5.62  tff(c_14879, plain, (![A_418, B_419]: (r2_hidden(A_418, k3_xboole_0(k1_tarski(A_418), B_419)) | ~r2_hidden(A_418, B_419))), inference(resolution, [status(thm)], [c_14807, c_68])).
% 13.27/5.62  tff(c_56, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.27/5.62  tff(c_48, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.27/5.62  tff(c_782, plain, (![A_104, C_105, B_106]: (~r2_hidden(A_104, C_105) | ~r2_hidden(A_104, B_106) | ~r2_hidden(A_104, k5_xboole_0(B_106, C_105)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.27/5.62  tff(c_6182, plain, (![A_260, A_261, B_262]: (~r2_hidden(A_260, k3_xboole_0(A_261, B_262)) | ~r2_hidden(A_260, A_261) | ~r2_hidden(A_260, k4_xboole_0(A_261, B_262)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_782])).
% 13.27/5.62  tff(c_21987, plain, (![A_568, A_569]: (~r2_hidden(A_568, k3_xboole_0(A_569, k1_xboole_0)) | ~r2_hidden(A_568, A_569) | ~r2_hidden(A_568, A_569))), inference(superposition, [status(thm), theory('equality')], [c_56, c_6182])).
% 13.27/5.62  tff(c_22087, plain, (![A_418]: (~r2_hidden(A_418, k1_tarski(A_418)) | ~r2_hidden(A_418, k1_xboole_0))), inference(resolution, [status(thm)], [c_14879, c_21987])).
% 13.27/5.62  tff(c_22308, plain, (![A_570]: (~r2_hidden(A_570, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_22087])).
% 13.27/5.62  tff(c_22498, plain, (![B_179]: (k3_xboole_0(k1_xboole_0, B_179)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3096, c_22308])).
% 13.27/5.62  tff(c_293, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.27/5.62  tff(c_308, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_293])).
% 13.27/5.62  tff(c_4473, plain, (![B_229, A_228]: (k5_xboole_0(B_229, k3_xboole_0(A_228, B_229))=k4_xboole_0(B_229, k3_xboole_0(A_228, B_229)))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_308])).
% 13.27/5.62  tff(c_4527, plain, (![B_229, A_228]: (k4_xboole_0(B_229, k3_xboole_0(A_228, B_229))=k4_xboole_0(B_229, A_228))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_4473])).
% 13.27/5.62  tff(c_140, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.27/5.62  tff(c_156, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_140, c_50])).
% 13.27/5.62  tff(c_376, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), B_82)=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.27/5.62  tff(c_418, plain, (![A_83]: (k4_xboole_0(k1_xboole_0, A_83)=k4_xboole_0(A_83, A_83))), inference(superposition, [status(thm), theory('equality')], [c_156, c_376])).
% 13.27/5.62  tff(c_54, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.27/5.62  tff(c_430, plain, (![A_83]: (k2_xboole_0(A_83, k4_xboole_0(A_83, A_83))=k2_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_418, c_54])).
% 13.27/5.62  tff(c_457, plain, (![A_87]: (k2_xboole_0(A_87, k4_xboole_0(A_87, A_87))=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_430])).
% 13.27/5.62  tff(c_466, plain, (![A_87]: (k2_xboole_0(A_87, A_87)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_457, c_54])).
% 13.27/5.62  tff(c_398, plain, (![A_52]: (k4_xboole_0(k1_xboole_0, A_52)=k4_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_156, c_376])).
% 13.27/5.62  tff(c_4751, plain, (![B_234, A_235]: (k3_xboole_0(B_234, k3_xboole_0(A_235, B_234))=k3_xboole_0(A_235, B_234))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_4])).
% 13.27/5.62  tff(c_4760, plain, (![A_235, B_234]: (k4_xboole_0(k3_xboole_0(A_235, B_234), k3_xboole_0(A_235, B_234))=k4_xboole_0(k3_xboole_0(A_235, B_234), B_234))), inference(superposition, [status(thm), theory('equality')], [c_4751, c_4527])).
% 13.27/5.62  tff(c_8732, plain, (![A_319, B_320]: (k4_xboole_0(k3_xboole_0(A_319, B_320), B_320)=k4_xboole_0(k1_xboole_0, k3_xboole_0(A_319, B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_4760])).
% 13.27/5.62  tff(c_8906, plain, (![A_323]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_323, k1_xboole_0))=k3_xboole_0(A_323, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8732, c_56])).
% 13.27/5.62  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.27/5.62  tff(c_5338, plain, (![A_247, B_248]: (k4_xboole_0(k2_xboole_0(A_247, B_248), k4_xboole_0(B_248, A_247))=k4_xboole_0(A_247, k4_xboole_0(B_248, A_247)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_376])).
% 13.27/5.62  tff(c_5464, plain, (![A_52]: (k4_xboole_0(k2_xboole_0(A_52, k1_xboole_0), k4_xboole_0(A_52, A_52))=k4_xboole_0(A_52, k4_xboole_0(k1_xboole_0, A_52)))), inference(superposition, [status(thm), theory('equality')], [c_398, c_5338])).
% 13.27/5.62  tff(c_6950, plain, (![A_289]: (k4_xboole_0(A_289, k4_xboole_0(k1_xboole_0, A_289))=k4_xboole_0(A_289, k4_xboole_0(A_289, A_289)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5464])).
% 13.27/5.62  tff(c_7061, plain, (![A_289]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_289), k4_xboole_0(A_289, k4_xboole_0(A_289, A_289)))=k2_xboole_0(k4_xboole_0(k1_xboole_0, A_289), A_289))), inference(superposition, [status(thm), theory('equality')], [c_6950, c_54])).
% 13.27/5.62  tff(c_7224, plain, (![A_293]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_293), k4_xboole_0(A_293, k4_xboole_0(A_293, A_293)))=A_293)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54, c_2, c_7061])).
% 13.27/5.62  tff(c_7315, plain, (![A_52]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_52), k4_xboole_0(A_52, k4_xboole_0(k1_xboole_0, A_52)))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_398, c_7224])).
% 13.27/5.62  tff(c_8918, plain, (![A_323]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, k3_xboole_0(A_323, k1_xboole_0)), k4_xboole_0(k3_xboole_0(A_323, k1_xboole_0), k3_xboole_0(A_323, k1_xboole_0)))=k3_xboole_0(A_323, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8906, c_7315])).
% 13.27/5.62  tff(c_9062, plain, (![A_323]: (k4_xboole_0(k1_xboole_0, A_323)=k3_xboole_0(A_323, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4527, c_466, c_398, c_8918])).
% 13.27/5.62  tff(c_263, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.27/5.62  tff(c_267, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_46, c_263])).
% 13.27/5.62  tff(c_302, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k4_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_267, c_293])).
% 13.27/5.62  tff(c_1115, plain, (![A_124, B_125]: (k5_xboole_0(k1_tarski(A_124), k1_tarski(A_124))=k4_xboole_0(k1_tarski(A_124), B_125) | ~r2_hidden(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_48])).
% 13.27/5.62  tff(c_1142, plain, (![A_124, B_125]: (k4_xboole_0(k1_tarski(A_124), B_125)=k4_xboole_0(k1_xboole_0, k1_tarski(A_124)) | ~r2_hidden(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_302, c_1115])).
% 13.27/5.62  tff(c_21641, plain, (![A_124, B_125]: (k4_xboole_0(k1_tarski(A_124), B_125)=k3_xboole_0(k1_xboole_0, k1_tarski(A_124)) | ~r2_hidden(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_9062, c_1142])).
% 13.27/5.62  tff(c_26195, plain, (![A_654, B_655]: (k4_xboole_0(k1_tarski(A_654), B_655)=k1_xboole_0 | ~r2_hidden(A_654, B_655))), inference(demodulation, [status(thm), theory('equality')], [c_22498, c_21641])).
% 13.27/5.62  tff(c_26288, plain, (![B_655, A_654]: (k2_xboole_0(B_655, k1_tarski(A_654))=k2_xboole_0(B_655, k1_xboole_0) | ~r2_hidden(A_654, B_655))), inference(superposition, [status(thm), theory('equality')], [c_26195, c_54])).
% 13.27/5.62  tff(c_26918, plain, (![B_662, A_663]: (k2_xboole_0(B_662, k1_tarski(A_663))=B_662 | ~r2_hidden(A_663, B_662))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26288])).
% 13.27/5.62  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.27/5.62  tff(c_78, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_74])).
% 13.27/5.62  tff(c_27001, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26918, c_78])).
% 13.27/5.62  tff(c_27044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_27001])).
% 13.27/5.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.27/5.62  
% 13.27/5.62  Inference rules
% 13.27/5.62  ----------------------
% 13.27/5.62  #Ref     : 0
% 13.27/5.62  #Sup     : 6489
% 13.27/5.62  #Fact    : 10
% 13.27/5.62  #Define  : 0
% 13.27/5.62  #Split   : 3
% 13.27/5.62  #Chain   : 0
% 13.27/5.62  #Close   : 0
% 13.27/5.62  
% 13.27/5.62  Ordering : KBO
% 13.27/5.62  
% 13.27/5.62  Simplification rules
% 13.27/5.62  ----------------------
% 13.27/5.62  #Subsume      : 1390
% 13.27/5.62  #Demod        : 9646
% 13.27/5.62  #Tautology    : 2759
% 13.27/5.62  #SimpNegUnit  : 90
% 13.27/5.62  #BackRed      : 64
% 13.27/5.62  
% 13.27/5.62  #Partial instantiations: 0
% 13.27/5.62  #Strategies tried      : 1
% 13.27/5.62  
% 13.27/5.62  Timing (in seconds)
% 13.27/5.62  ----------------------
% 13.27/5.63  Preprocessing        : 0.33
% 13.27/5.63  Parsing              : 0.17
% 13.27/5.63  CNF conversion       : 0.02
% 13.27/5.63  Main loop            : 4.53
% 13.27/5.63  Inferencing          : 0.91
% 13.27/5.63  Reduction            : 2.24
% 13.27/5.63  Demodulation         : 1.96
% 13.27/5.63  BG Simplification    : 0.10
% 13.27/5.63  Subsumption          : 1.05
% 13.27/5.63  Abstraction          : 0.17
% 13.27/5.63  MUC search           : 0.00
% 13.27/5.63  Cooper               : 0.00
% 13.27/5.63  Total                : 4.90
% 13.27/5.63  Index Insertion      : 0.00
% 13.27/5.63  Index Deletion       : 0.00
% 13.27/5.63  Index Matching       : 0.00
% 13.27/5.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
