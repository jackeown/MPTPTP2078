%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:10 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 285 expanded)
%              Number of leaves         :   40 ( 106 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 ( 520 expanded)
%              Number of equality atoms :   94 ( 390 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_78,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_109,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_94,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_111,plain,(
    ! [A_69,B_70] : r1_tarski(A_69,k2_xboole_0(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_114,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_111])).

tff(c_945,plain,(
    ! [B_128,A_129] :
      ( k1_tarski(B_128) = A_129
      | k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,k1_tarski(B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_960,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_114,c_945])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_94,c_960])).

tff(c_973,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1150,plain,(
    ! [A_142,B_143] :
      ( k3_xboole_0(A_142,B_143) = A_142
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1214,plain,(
    ! [A_149,B_150] : k3_xboole_0(A_149,k2_xboole_0(A_149,B_150)) = A_149 ),
    inference(resolution,[status(thm)],[c_34,c_1150])).

tff(c_28,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1236,plain,(
    ! [A_151] : r1_tarski(A_151,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_28])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1240,plain,(
    ! [A_151] : k3_xboole_0(A_151,A_151) = A_151 ),
    inference(resolution,[status(thm)],[c_1236,c_30])).

tff(c_974,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1200,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_14])).

tff(c_1434,plain,(
    ! [A_170,B_171,C_172] :
      ( ~ r1_xboole_0(A_170,B_171)
      | ~ r2_hidden(C_172,k3_xboole_0(A_170,B_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1455,plain,(
    ! [A_173,C_174] :
      ( ~ r1_xboole_0(A_173,A_173)
      | ~ r2_hidden(C_174,A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1240,c_1434])).

tff(c_1458,plain,(
    ! [C_174,B_11] :
      ( ~ r2_hidden(C_174,B_11)
      | k3_xboole_0(B_11,B_11) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1200,c_1455])).

tff(c_1511,plain,(
    ! [C_179,B_180] :
      ( ~ r2_hidden(C_179,B_180)
      | B_180 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1458])).

tff(c_1525,plain,(
    ! [A_183,B_184] :
      ( A_183 != '#skF_4'
      | r1_tarski(A_183,B_184) ) ),
    inference(resolution,[status(thm)],[c_10,c_1511])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1780,plain,(
    ! [B_184] : k2_xboole_0('#skF_4',B_184) = B_184 ),
    inference(resolution,[status(thm)],[c_1525,c_24])).

tff(c_1782,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_66])).

tff(c_1784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1782])).

tff(c_1785,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1786,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1801,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1786,c_64])).

tff(c_1795,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_66])).

tff(c_32,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [B_59] : r1_tarski(k1_xboole_0,k1_tarski(B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1789,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_56])).

tff(c_1973,plain,(
    ! [A_213,B_214] :
      ( k3_xboole_0(A_213,B_214) = A_213
      | ~ r1_tarski(A_213,B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2000,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1789,c_1973])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2021,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_2])).

tff(c_2617,plain,(
    ! [A_252,B_253,C_254] :
      ( ~ r1_xboole_0(A_252,B_253)
      | ~ r2_hidden(C_254,k3_xboole_0(A_252,B_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2636,plain,(
    ! [C_254] :
      ( ~ r1_xboole_0(k1_xboole_0,'#skF_4')
      | ~ r2_hidden(C_254,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_2617])).

tff(c_2644,plain,(
    ~ r1_xboole_0(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_2647,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_2644])).

tff(c_2651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2021,c_2,c_2647])).

tff(c_2654,plain,(
    ! [C_255] : ~ r2_hidden(C_255,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_2667,plain,(
    ! [B_256] : r1_tarski(k1_xboole_0,B_256) ),
    inference(resolution,[status(thm)],[c_10,c_2654])).

tff(c_2714,plain,(
    ! [B_261] : k3_xboole_0(k1_xboole_0,B_261) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2667,c_30])).

tff(c_2811,plain,(
    ! [B_263] : k3_xboole_0(B_263,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2714,c_2])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2828,plain,(
    ! [B_263] : k5_xboole_0(B_263,k1_xboole_0) = k4_xboole_0(B_263,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2811,c_22])).

tff(c_2872,plain,(
    ! [B_263] : k4_xboole_0(B_263,k1_xboole_0) = B_263 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2828])).

tff(c_2889,plain,(
    ! [B_264,A_265] :
      ( k1_tarski(B_264) = A_265
      | k1_xboole_0 = A_265
      | ~ r1_tarski(A_265,k1_tarski(B_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2908,plain,(
    ! [A_265] :
      ( k1_tarski('#skF_3') = A_265
      | k1_xboole_0 = A_265
      | ~ r1_tarski(A_265,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_2889])).

tff(c_2919,plain,(
    ! [A_266] :
      ( A_266 = '#skF_4'
      | k1_xboole_0 = A_266
      | ~ r1_tarski(A_266,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_2908])).

tff(c_2945,plain,(
    ! [B_27] :
      ( k3_xboole_0('#skF_4',B_27) = '#skF_4'
      | k3_xboole_0('#skF_4',B_27) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_2919])).

tff(c_4775,plain,(
    ! [A_320,B_321] : k4_xboole_0(k2_xboole_0(A_320,B_321),k3_xboole_0(A_320,B_321)) = k5_xboole_0(A_320,B_321) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4838,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_4775])).

tff(c_4956,plain,
    ( k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4',k1_xboole_0)
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2945,c_4838])).

tff(c_4968,plain,
    ( k5_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2872,c_4956])).

tff(c_5489,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4968])).

tff(c_2087,plain,(
    ! [A_218,B_219] :
      ( k2_xboole_0(A_218,B_219) = B_219
      | ~ r1_tarski(A_218,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2247,plain,(
    ! [A_229,B_230] : k2_xboole_0(k3_xboole_0(A_229,B_230),A_229) = A_229 ),
    inference(resolution,[status(thm)],[c_28,c_2087])).

tff(c_2280,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2247])).

tff(c_5550,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5489,c_2280])).

tff(c_5580,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1795,c_5550])).

tff(c_5582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1801,c_5580])).

tff(c_5583,plain,(
    k5_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4968])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1827,plain,(
    ! [B_206,A_207] : k5_xboole_0(B_206,A_207) = k5_xboole_0(A_207,B_206) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1843,plain,(
    ! [A_207] : k5_xboole_0(k1_xboole_0,A_207) = A_207 ),
    inference(superposition,[status(thm),theory(equality)],[c_1827,c_32])).

tff(c_38,plain,(
    ! [A_36] : k5_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3379,plain,(
    ! [A_286,B_287,C_288] : k5_xboole_0(k5_xboole_0(A_286,B_287),C_288) = k5_xboole_0(A_286,k5_xboole_0(B_287,C_288)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3436,plain,(
    ! [A_36,C_288] : k5_xboole_0(A_36,k5_xboole_0(A_36,C_288)) = k5_xboole_0(k1_xboole_0,C_288) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3379])).

tff(c_3457,plain,(
    ! [A_289,C_290] : k5_xboole_0(A_289,k5_xboole_0(A_289,C_290)) = C_290 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3436])).

tff(c_3522,plain,(
    ! [A_291,B_292] : k5_xboole_0(A_291,k5_xboole_0(B_292,A_291)) = B_292 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3457])).

tff(c_3500,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3457])).

tff(c_3525,plain,(
    ! [B_292,A_291] : k5_xboole_0(k5_xboole_0(B_292,A_291),B_292) = A_291 ),
    inference(superposition,[status(thm),theory(equality)],[c_3522,c_3500])).

tff(c_5592,plain,(
    k5_xboole_0('#skF_4','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5583,c_3525])).

tff(c_5635,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5592,c_38])).

tff(c_5644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1785,c_5635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.98  
% 4.99/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.99/1.98  
% 4.99/1.98  %Foreground sorts:
% 4.99/1.98  
% 4.99/1.98  
% 4.99/1.98  %Background operators:
% 4.99/1.98  
% 4.99/1.98  
% 4.99/1.98  %Foreground operators:
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.99/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.99/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.99/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.99/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.99/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.99/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.99/1.98  tff('#skF_5', type, '#skF_5': $i).
% 4.99/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.99/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.99/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.99/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.99/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.99/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.99/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.99/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.99/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.99/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.99/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.99/1.98  
% 4.99/2.00  tff(f_117, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.99/2.00  tff(f_74, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.99/2.00  tff(f_96, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.99/2.00  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.99/2.00  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.99/2.00  tff(f_66, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.99/2.00  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.99/2.00  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.99/2.00  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.99/2.00  tff(f_72, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.99/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.99/2.00  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.99/2.00  tff(f_56, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.99/2.00  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.99/2.00  tff(f_78, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.99/2.00  tff(f_76, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.99/2.00  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.99/2.00  tff(c_109, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 4.99/2.00  tff(c_60, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.99/2.00  tff(c_94, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 4.99/2.00  tff(c_66, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.99/2.00  tff(c_111, plain, (![A_69, B_70]: (r1_tarski(A_69, k2_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.99/2.00  tff(c_114, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_111])).
% 4.99/2.00  tff(c_945, plain, (![B_128, A_129]: (k1_tarski(B_128)=A_129 | k1_xboole_0=A_129 | ~r1_tarski(A_129, k1_tarski(B_128)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.99/2.00  tff(c_960, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_114, c_945])).
% 4.99/2.00  tff(c_972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_94, c_960])).
% 4.99/2.00  tff(c_973, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 4.99/2.00  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.99/2.00  tff(c_34, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.99/2.00  tff(c_1150, plain, (![A_142, B_143]: (k3_xboole_0(A_142, B_143)=A_142 | ~r1_tarski(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.00  tff(c_1214, plain, (![A_149, B_150]: (k3_xboole_0(A_149, k2_xboole_0(A_149, B_150))=A_149)), inference(resolution, [status(thm)], [c_34, c_1150])).
% 4.99/2.00  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/2.00  tff(c_1236, plain, (![A_151]: (r1_tarski(A_151, A_151))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_28])).
% 4.99/2.00  tff(c_30, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.00  tff(c_1240, plain, (![A_151]: (k3_xboole_0(A_151, A_151)=A_151)), inference(resolution, [status(thm)], [c_1236, c_30])).
% 4.99/2.00  tff(c_974, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 4.99/2.00  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.99/2.00  tff(c_1200, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_14])).
% 4.99/2.00  tff(c_1434, plain, (![A_170, B_171, C_172]: (~r1_xboole_0(A_170, B_171) | ~r2_hidden(C_172, k3_xboole_0(A_170, B_171)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.99/2.00  tff(c_1455, plain, (![A_173, C_174]: (~r1_xboole_0(A_173, A_173) | ~r2_hidden(C_174, A_173))), inference(superposition, [status(thm), theory('equality')], [c_1240, c_1434])).
% 4.99/2.00  tff(c_1458, plain, (![C_174, B_11]: (~r2_hidden(C_174, B_11) | k3_xboole_0(B_11, B_11)!='#skF_4')), inference(resolution, [status(thm)], [c_1200, c_1455])).
% 4.99/2.00  tff(c_1511, plain, (![C_179, B_180]: (~r2_hidden(C_179, B_180) | B_180!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1458])).
% 4.99/2.00  tff(c_1525, plain, (![A_183, B_184]: (A_183!='#skF_4' | r1_tarski(A_183, B_184))), inference(resolution, [status(thm)], [c_10, c_1511])).
% 4.99/2.00  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.99/2.00  tff(c_1780, plain, (![B_184]: (k2_xboole_0('#skF_4', B_184)=B_184)), inference(resolution, [status(thm)], [c_1525, c_24])).
% 4.99/2.00  tff(c_1782, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_66])).
% 4.99/2.00  tff(c_1784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1782])).
% 4.99/2.00  tff(c_1785, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 4.99/2.00  tff(c_1786, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 4.99/2.00  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.99/2.00  tff(c_1801, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1786, c_64])).
% 4.99/2.00  tff(c_1795, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_66])).
% 4.99/2.00  tff(c_32, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.99/2.00  tff(c_56, plain, (![B_59]: (r1_tarski(k1_xboole_0, k1_tarski(B_59)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.99/2.00  tff(c_1789, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1786, c_56])).
% 4.99/2.00  tff(c_1973, plain, (![A_213, B_214]: (k3_xboole_0(A_213, B_214)=A_213 | ~r1_tarski(A_213, B_214))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.99/2.00  tff(c_2000, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1789, c_1973])).
% 4.99/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.99/2.00  tff(c_2021, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2000, c_2])).
% 4.99/2.00  tff(c_2617, plain, (![A_252, B_253, C_254]: (~r1_xboole_0(A_252, B_253) | ~r2_hidden(C_254, k3_xboole_0(A_252, B_253)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.99/2.00  tff(c_2636, plain, (![C_254]: (~r1_xboole_0(k1_xboole_0, '#skF_4') | ~r2_hidden(C_254, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2000, c_2617])).
% 4.99/2.00  tff(c_2644, plain, (~r1_xboole_0(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_2636])).
% 4.99/2.00  tff(c_2647, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_2644])).
% 4.99/2.00  tff(c_2651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2021, c_2, c_2647])).
% 4.99/2.00  tff(c_2654, plain, (![C_255]: (~r2_hidden(C_255, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2636])).
% 4.99/2.00  tff(c_2667, plain, (![B_256]: (r1_tarski(k1_xboole_0, B_256))), inference(resolution, [status(thm)], [c_10, c_2654])).
% 4.99/2.00  tff(c_2714, plain, (![B_261]: (k3_xboole_0(k1_xboole_0, B_261)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2667, c_30])).
% 4.99/2.00  tff(c_2811, plain, (![B_263]: (k3_xboole_0(B_263, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2714, c_2])).
% 4.99/2.00  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.99/2.00  tff(c_2828, plain, (![B_263]: (k5_xboole_0(B_263, k1_xboole_0)=k4_xboole_0(B_263, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2811, c_22])).
% 4.99/2.00  tff(c_2872, plain, (![B_263]: (k4_xboole_0(B_263, k1_xboole_0)=B_263)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2828])).
% 4.99/2.00  tff(c_2889, plain, (![B_264, A_265]: (k1_tarski(B_264)=A_265 | k1_xboole_0=A_265 | ~r1_tarski(A_265, k1_tarski(B_264)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.99/2.00  tff(c_2908, plain, (![A_265]: (k1_tarski('#skF_3')=A_265 | k1_xboole_0=A_265 | ~r1_tarski(A_265, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1786, c_2889])).
% 4.99/2.00  tff(c_2919, plain, (![A_266]: (A_266='#skF_4' | k1_xboole_0=A_266 | ~r1_tarski(A_266, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_2908])).
% 4.99/2.00  tff(c_2945, plain, (![B_27]: (k3_xboole_0('#skF_4', B_27)='#skF_4' | k3_xboole_0('#skF_4', B_27)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_2919])).
% 4.99/2.00  tff(c_4775, plain, (![A_320, B_321]: (k4_xboole_0(k2_xboole_0(A_320, B_321), k3_xboole_0(A_320, B_321))=k5_xboole_0(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.99/2.00  tff(c_4838, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1795, c_4775])).
% 4.99/2.00  tff(c_4956, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', k1_xboole_0) | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2945, c_4838])).
% 4.99/2.00  tff(c_4968, plain, (k5_xboole_0('#skF_4', '#skF_5')='#skF_4' | k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2872, c_4956])).
% 4.99/2.00  tff(c_5489, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_4968])).
% 4.99/2.00  tff(c_2087, plain, (![A_218, B_219]: (k2_xboole_0(A_218, B_219)=B_219 | ~r1_tarski(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.99/2.00  tff(c_2247, plain, (![A_229, B_230]: (k2_xboole_0(k3_xboole_0(A_229, B_230), A_229)=A_229)), inference(resolution, [status(thm)], [c_28, c_2087])).
% 4.99/2.00  tff(c_2280, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2247])).
% 4.99/2.00  tff(c_5550, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5489, c_2280])).
% 4.99/2.00  tff(c_5580, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1795, c_5550])).
% 4.99/2.00  tff(c_5582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1801, c_5580])).
% 4.99/2.00  tff(c_5583, plain, (k5_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_4968])).
% 4.99/2.00  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/2.00  tff(c_1827, plain, (![B_206, A_207]: (k5_xboole_0(B_206, A_207)=k5_xboole_0(A_207, B_206))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.99/2.00  tff(c_1843, plain, (![A_207]: (k5_xboole_0(k1_xboole_0, A_207)=A_207)), inference(superposition, [status(thm), theory('equality')], [c_1827, c_32])).
% 4.99/2.00  tff(c_38, plain, (![A_36]: (k5_xboole_0(A_36, A_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.99/2.00  tff(c_3379, plain, (![A_286, B_287, C_288]: (k5_xboole_0(k5_xboole_0(A_286, B_287), C_288)=k5_xboole_0(A_286, k5_xboole_0(B_287, C_288)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.99/2.00  tff(c_3436, plain, (![A_36, C_288]: (k5_xboole_0(A_36, k5_xboole_0(A_36, C_288))=k5_xboole_0(k1_xboole_0, C_288))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3379])).
% 4.99/2.00  tff(c_3457, plain, (![A_289, C_290]: (k5_xboole_0(A_289, k5_xboole_0(A_289, C_290))=C_290)), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3436])).
% 4.99/2.00  tff(c_3522, plain, (![A_291, B_292]: (k5_xboole_0(A_291, k5_xboole_0(B_292, A_291))=B_292)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3457])).
% 4.99/2.00  tff(c_3500, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3457])).
% 4.99/2.00  tff(c_3525, plain, (![B_292, A_291]: (k5_xboole_0(k5_xboole_0(B_292, A_291), B_292)=A_291)), inference(superposition, [status(thm), theory('equality')], [c_3522, c_3500])).
% 4.99/2.00  tff(c_5592, plain, (k5_xboole_0('#skF_4', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5583, c_3525])).
% 4.99/2.00  tff(c_5635, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5592, c_38])).
% 4.99/2.00  tff(c_5644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1785, c_5635])).
% 4.99/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.99/2.00  
% 4.99/2.00  Inference rules
% 4.99/2.00  ----------------------
% 4.99/2.00  #Ref     : 1
% 4.99/2.00  #Sup     : 1366
% 4.99/2.00  #Fact    : 4
% 4.99/2.00  #Define  : 0
% 4.99/2.00  #Split   : 6
% 4.99/2.00  #Chain   : 0
% 4.99/2.00  #Close   : 0
% 4.99/2.00  
% 4.99/2.00  Ordering : KBO
% 4.99/2.00  
% 4.99/2.00  Simplification rules
% 4.99/2.00  ----------------------
% 4.99/2.00  #Subsume      : 130
% 4.99/2.00  #Demod        : 650
% 4.99/2.00  #Tautology    : 903
% 4.99/2.00  #SimpNegUnit  : 37
% 4.99/2.00  #BackRed      : 10
% 4.99/2.00  
% 4.99/2.00  #Partial instantiations: 0
% 4.99/2.00  #Strategies tried      : 1
% 4.99/2.00  
% 4.99/2.00  Timing (in seconds)
% 4.99/2.00  ----------------------
% 4.99/2.00  Preprocessing        : 0.34
% 4.99/2.00  Parsing              : 0.18
% 4.99/2.00  CNF conversion       : 0.02
% 4.99/2.00  Main loop            : 0.87
% 4.99/2.00  Inferencing          : 0.29
% 4.99/2.00  Reduction            : 0.35
% 4.99/2.00  Demodulation         : 0.27
% 4.99/2.00  BG Simplification    : 0.04
% 4.99/2.00  Subsumption          : 0.13
% 4.99/2.00  Abstraction          : 0.04
% 4.99/2.00  MUC search           : 0.00
% 4.99/2.00  Cooper               : 0.00
% 4.99/2.00  Total                : 1.25
% 4.99/2.00  Index Insertion      : 0.00
% 4.99/2.00  Index Deletion       : 0.00
% 4.99/2.00  Index Matching       : 0.00
% 4.99/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
