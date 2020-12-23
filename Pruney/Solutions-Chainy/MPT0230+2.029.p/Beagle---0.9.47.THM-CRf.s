%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:01 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 212 expanded)
%              Number of leaves         :   44 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  101 ( 221 expanded)
%              Number of equality atoms :   85 ( 180 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_84,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_72,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    ! [A_48,B_49,C_50,D_51] : k3_enumset1(A_48,A_48,B_49,C_50,D_51) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2632,plain,(
    ! [D_188,C_190,A_186,E_189,B_187] : k2_xboole_0(k2_enumset1(A_186,B_187,C_190,D_188),k1_tarski(E_189)) = k3_enumset1(A_186,B_187,C_190,D_188,E_189) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2641,plain,(
    ! [A_45,B_46,C_47,E_189] : k3_enumset1(A_45,A_45,B_46,C_47,E_189) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),k1_tarski(E_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2632])).

tff(c_5268,plain,(
    ! [A_302,B_303,C_304,E_305] : k2_xboole_0(k1_enumset1(A_302,B_303,C_304),k1_tarski(E_305)) = k2_enumset1(A_302,B_303,C_304,E_305) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2641])).

tff(c_5292,plain,(
    ! [A_43,B_44,E_305] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(E_305)) = k2_enumset1(A_43,A_43,B_44,E_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_5268])).

tff(c_5959,plain,(
    ! [A_328,B_329,E_330] : k2_xboole_0(k2_tarski(A_328,B_329),k1_tarski(E_330)) = k1_enumset1(A_328,B_329,E_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5292])).

tff(c_88,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_304,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(A_101,B_102) = A_101
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_325,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_304])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_164,plain,(
    ! [B_86,A_87] : k3_xboole_0(B_86,A_87) = k3_xboole_0(A_87,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_122,plain,(
    ! [A_80,B_81] : r1_tarski(k3_xboole_0(A_80,B_81),A_80) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [B_81] : k3_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_12])).

tff(c_180,plain,(
    ! [B_86] : k3_xboole_0(B_86,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_130])).

tff(c_348,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,(
    ! [B_86] : k5_xboole_0(B_86,k1_xboole_0) = k4_xboole_0(B_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_348])).

tff(c_372,plain,(
    ! [B_86] : k4_xboole_0(B_86,k1_xboole_0) = B_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_357])).

tff(c_639,plain,(
    ! [A_119,B_120] : k4_xboole_0(A_119,k4_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_664,plain,(
    ! [B_86] : k4_xboole_0(B_86,B_86) = k3_xboole_0(B_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_639])).

tff(c_676,plain,(
    ! [B_86] : k4_xboole_0(B_86,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_664])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_369,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_348])).

tff(c_680,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_369])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_838,plain,(
    ! [A_129,B_130] : k3_xboole_0(k3_xboole_0(A_129,B_130),A_129) = k3_xboole_0(A_129,B_130) ),
    inference(resolution,[status(thm)],[c_8,c_304])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_850,plain,(
    ! [A_129,B_130] : k5_xboole_0(k3_xboole_0(A_129,B_130),k3_xboole_0(A_129,B_130)) = k4_xboole_0(k3_xboole_0(A_129,B_130),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_6])).

tff(c_917,plain,(
    ! [A_131,B_132] : k4_xboole_0(k3_xboole_0(A_131,B_132),A_131) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_850])).

tff(c_972,plain,(
    ! [B_133,A_134] : k4_xboole_0(k3_xboole_0(B_133,A_134),A_134) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_917])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_983,plain,(
    ! [A_134,B_133] : k2_xboole_0(A_134,k3_xboole_0(B_133,A_134)) = k5_xboole_0(A_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_18])).

tff(c_1069,plain,(
    ! [A_137,B_138] : k2_xboole_0(A_137,k3_xboole_0(B_138,A_137)) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_983])).

tff(c_1089,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_1069])).

tff(c_5973,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5959,c_1089])).

tff(c_22,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6020,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5973,c_22])).

tff(c_1563,plain,(
    ! [B_152,A_153,C_154] : k2_xboole_0(k2_tarski(B_152,A_153),k2_tarski(C_154,A_153)) = k1_enumset1(A_153,B_152,C_154) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_681,plain,(
    ! [B_121] : k4_xboole_0(B_121,B_121) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_664])).

tff(c_689,plain,(
    ! [B_121] : k5_xboole_0(B_121,k1_xboole_0) = k2_xboole_0(B_121,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_18])).

tff(c_708,plain,(
    ! [B_121] : k2_xboole_0(B_121,B_121) = B_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_689])).

tff(c_1570,plain,(
    ! [A_153,C_154] : k1_enumset1(A_153,C_154,C_154) = k2_tarski(C_154,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_708])).

tff(c_68,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2267,plain,(
    ! [A_171,B_172,C_173,D_174] : k2_xboole_0(k2_tarski(A_171,B_172),k2_tarski(C_173,D_174)) = k2_enumset1(A_171,B_172,C_173,D_174) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2291,plain,(
    ! [A_42,C_173,D_174] : k2_xboole_0(k1_tarski(A_42),k2_tarski(C_173,D_174)) = k2_enumset1(A_42,A_42,C_173,D_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2267])).

tff(c_3728,plain,(
    ! [A_261,C_262,D_263] : k2_xboole_0(k1_tarski(A_261),k2_tarski(C_262,D_263)) = k1_enumset1(A_261,C_262,D_263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2291])).

tff(c_3744,plain,(
    ! [A_261,A_42] : k2_xboole_0(k1_tarski(A_261),k1_tarski(A_42)) = k1_enumset1(A_261,A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3728])).

tff(c_3749,plain,(
    ! [A_261,A_42] : k2_xboole_0(k1_tarski(A_261),k1_tarski(A_42)) = k2_tarski(A_42,A_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1570,c_3744])).

tff(c_2947,plain,(
    ! [A_207,B_208] : k2_enumset1(A_207,B_208,A_207,B_208) = k2_tarski(A_207,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_2267])).

tff(c_2957,plain,(
    ! [B_208] : k1_enumset1(B_208,B_208,B_208) = k2_tarski(B_208,B_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_2947,c_72])).

tff(c_2966,plain,(
    ! [B_208] : k1_enumset1(B_208,B_208,B_208) = k1_tarski(B_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2957])).

tff(c_5277,plain,(
    ! [B_208,E_305] : k2_xboole_0(k1_tarski(B_208),k1_tarski(E_305)) = k2_enumset1(B_208,B_208,B_208,E_305) ),
    inference(superposition,[status(thm),theory(equality)],[c_2966,c_5268])).

tff(c_5297,plain,(
    ! [B_306,E_307] : k2_enumset1(B_306,B_306,B_306,E_307) = k2_tarski(E_307,B_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3749,c_5277])).

tff(c_5366,plain,(
    ! [B_308,E_309] : k1_enumset1(B_308,B_308,E_309) = k2_tarski(E_309,B_308) ),
    inference(superposition,[status(thm),theory(equality)],[c_5297,c_72])).

tff(c_5443,plain,(
    ! [E_310,B_311] : k2_tarski(E_310,B_311) = k2_tarski(B_311,E_310) ),
    inference(superposition,[status(thm),theory(equality)],[c_5366,c_70])).

tff(c_44,plain,(
    ! [D_29,B_25,A_24] :
      ( D_29 = B_25
      | D_29 = A_24
      | ~ r2_hidden(D_29,k2_tarski(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5509,plain,(
    ! [D_29,B_311,E_310] :
      ( D_29 = B_311
      | E_310 = D_29
      | ~ r2_hidden(D_29,k2_tarski(B_311,E_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5443,c_44])).

tff(c_6041,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6020,c_5509])).

tff(c_6048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_86,c_6041])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.12  
% 5.55/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.13  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 5.55/2.13  
% 5.55/2.13  %Foreground sorts:
% 5.55/2.13  
% 5.55/2.13  
% 5.55/2.13  %Background operators:
% 5.55/2.13  
% 5.55/2.13  
% 5.55/2.13  %Foreground operators:
% 5.55/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.55/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.55/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.55/2.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.55/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.55/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.55/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.55/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.55/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.55/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.55/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.55/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.55/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.55/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.55/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.55/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.55/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.55/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.55/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.55/2.13  
% 5.55/2.15  tff(f_103, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 5.55/2.15  tff(f_83, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.55/2.15  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.55/2.15  tff(f_85, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 5.55/2.15  tff(f_77, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 5.55/2.15  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.55/2.15  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.55/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.55/2.15  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.55/2.15  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.55/2.15  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.55/2.15  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.55/2.15  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.55/2.15  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.55/2.15  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.55/2.15  tff(f_75, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 5.55/2.15  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.55/2.15  tff(f_73, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 5.55/2.15  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.55/2.15  tff(c_84, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.55/2.15  tff(c_86, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.55/2.15  tff(c_72, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.55/2.15  tff(c_70, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.55/2.15  tff(c_74, plain, (![A_48, B_49, C_50, D_51]: (k3_enumset1(A_48, A_48, B_49, C_50, D_51)=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.55/2.15  tff(c_2632, plain, (![D_188, C_190, A_186, E_189, B_187]: (k2_xboole_0(k2_enumset1(A_186, B_187, C_190, D_188), k1_tarski(E_189))=k3_enumset1(A_186, B_187, C_190, D_188, E_189))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.55/2.15  tff(c_2641, plain, (![A_45, B_46, C_47, E_189]: (k3_enumset1(A_45, A_45, B_46, C_47, E_189)=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), k1_tarski(E_189)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2632])).
% 5.55/2.15  tff(c_5268, plain, (![A_302, B_303, C_304, E_305]: (k2_xboole_0(k1_enumset1(A_302, B_303, C_304), k1_tarski(E_305))=k2_enumset1(A_302, B_303, C_304, E_305))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2641])).
% 5.55/2.15  tff(c_5292, plain, (![A_43, B_44, E_305]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(E_305))=k2_enumset1(A_43, A_43, B_44, E_305))), inference(superposition, [status(thm), theory('equality')], [c_70, c_5268])).
% 5.55/2.15  tff(c_5959, plain, (![A_328, B_329, E_330]: (k2_xboole_0(k2_tarski(A_328, B_329), k1_tarski(E_330))=k1_enumset1(A_328, B_329, E_330))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5292])).
% 5.55/2.15  tff(c_88, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.55/2.15  tff(c_304, plain, (![A_101, B_102]: (k3_xboole_0(A_101, B_102)=A_101 | ~r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.15  tff(c_325, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_88, c_304])).
% 5.55/2.15  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.55/2.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.55/2.15  tff(c_164, plain, (![B_86, A_87]: (k3_xboole_0(B_86, A_87)=k3_xboole_0(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.55/2.15  tff(c_122, plain, (![A_80, B_81]: (r1_tarski(k3_xboole_0(A_80, B_81), A_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.55/2.15  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.55/2.15  tff(c_130, plain, (![B_81]: (k3_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_12])).
% 5.55/2.15  tff(c_180, plain, (![B_86]: (k3_xboole_0(B_86, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_164, c_130])).
% 5.55/2.15  tff(c_348, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.55/2.15  tff(c_357, plain, (![B_86]: (k5_xboole_0(B_86, k1_xboole_0)=k4_xboole_0(B_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_348])).
% 5.55/2.15  tff(c_372, plain, (![B_86]: (k4_xboole_0(B_86, k1_xboole_0)=B_86)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_357])).
% 5.55/2.15  tff(c_639, plain, (![A_119, B_120]: (k4_xboole_0(A_119, k4_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.55/2.15  tff(c_664, plain, (![B_86]: (k4_xboole_0(B_86, B_86)=k3_xboole_0(B_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_372, c_639])).
% 5.55/2.15  tff(c_676, plain, (![B_86]: (k4_xboole_0(B_86, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_664])).
% 5.55/2.15  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.55/2.15  tff(c_369, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_348])).
% 5.55/2.15  tff(c_680, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_676, c_369])).
% 5.55/2.15  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.55/2.15  tff(c_838, plain, (![A_129, B_130]: (k3_xboole_0(k3_xboole_0(A_129, B_130), A_129)=k3_xboole_0(A_129, B_130))), inference(resolution, [status(thm)], [c_8, c_304])).
% 5.55/2.15  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.55/2.15  tff(c_850, plain, (![A_129, B_130]: (k5_xboole_0(k3_xboole_0(A_129, B_130), k3_xboole_0(A_129, B_130))=k4_xboole_0(k3_xboole_0(A_129, B_130), A_129))), inference(superposition, [status(thm), theory('equality')], [c_838, c_6])).
% 5.55/2.15  tff(c_917, plain, (![A_131, B_132]: (k4_xboole_0(k3_xboole_0(A_131, B_132), A_131)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_680, c_850])).
% 5.55/2.15  tff(c_972, plain, (![B_133, A_134]: (k4_xboole_0(k3_xboole_0(B_133, A_134), A_134)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_917])).
% 5.55/2.15  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.55/2.15  tff(c_983, plain, (![A_134, B_133]: (k2_xboole_0(A_134, k3_xboole_0(B_133, A_134))=k5_xboole_0(A_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_972, c_18])).
% 5.55/2.15  tff(c_1069, plain, (![A_137, B_138]: (k2_xboole_0(A_137, k3_xboole_0(B_138, A_137))=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_983])).
% 5.55/2.15  tff(c_1089, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_325, c_1069])).
% 5.55/2.15  tff(c_5973, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5959, c_1089])).
% 5.55/2.15  tff(c_22, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.55/2.15  tff(c_6020, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5973, c_22])).
% 5.55/2.15  tff(c_1563, plain, (![B_152, A_153, C_154]: (k2_xboole_0(k2_tarski(B_152, A_153), k2_tarski(C_154, A_153))=k1_enumset1(A_153, B_152, C_154))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.55/2.15  tff(c_681, plain, (![B_121]: (k4_xboole_0(B_121, B_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_664])).
% 5.55/2.15  tff(c_689, plain, (![B_121]: (k5_xboole_0(B_121, k1_xboole_0)=k2_xboole_0(B_121, B_121))), inference(superposition, [status(thm), theory('equality')], [c_681, c_18])).
% 5.55/2.15  tff(c_708, plain, (![B_121]: (k2_xboole_0(B_121, B_121)=B_121)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_689])).
% 5.55/2.15  tff(c_1570, plain, (![A_153, C_154]: (k1_enumset1(A_153, C_154, C_154)=k2_tarski(C_154, A_153))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_708])).
% 5.55/2.15  tff(c_68, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.55/2.15  tff(c_2267, plain, (![A_171, B_172, C_173, D_174]: (k2_xboole_0(k2_tarski(A_171, B_172), k2_tarski(C_173, D_174))=k2_enumset1(A_171, B_172, C_173, D_174))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.55/2.15  tff(c_2291, plain, (![A_42, C_173, D_174]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(C_173, D_174))=k2_enumset1(A_42, A_42, C_173, D_174))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2267])).
% 5.55/2.15  tff(c_3728, plain, (![A_261, C_262, D_263]: (k2_xboole_0(k1_tarski(A_261), k2_tarski(C_262, D_263))=k1_enumset1(A_261, C_262, D_263))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2291])).
% 5.55/2.15  tff(c_3744, plain, (![A_261, A_42]: (k2_xboole_0(k1_tarski(A_261), k1_tarski(A_42))=k1_enumset1(A_261, A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_68, c_3728])).
% 5.55/2.15  tff(c_3749, plain, (![A_261, A_42]: (k2_xboole_0(k1_tarski(A_261), k1_tarski(A_42))=k2_tarski(A_42, A_261))), inference(demodulation, [status(thm), theory('equality')], [c_1570, c_3744])).
% 5.55/2.15  tff(c_2947, plain, (![A_207, B_208]: (k2_enumset1(A_207, B_208, A_207, B_208)=k2_tarski(A_207, B_208))), inference(superposition, [status(thm), theory('equality')], [c_708, c_2267])).
% 5.55/2.15  tff(c_2957, plain, (![B_208]: (k1_enumset1(B_208, B_208, B_208)=k2_tarski(B_208, B_208))), inference(superposition, [status(thm), theory('equality')], [c_2947, c_72])).
% 5.55/2.15  tff(c_2966, plain, (![B_208]: (k1_enumset1(B_208, B_208, B_208)=k1_tarski(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2957])).
% 5.55/2.15  tff(c_5277, plain, (![B_208, E_305]: (k2_xboole_0(k1_tarski(B_208), k1_tarski(E_305))=k2_enumset1(B_208, B_208, B_208, E_305))), inference(superposition, [status(thm), theory('equality')], [c_2966, c_5268])).
% 5.55/2.15  tff(c_5297, plain, (![B_306, E_307]: (k2_enumset1(B_306, B_306, B_306, E_307)=k2_tarski(E_307, B_306))), inference(demodulation, [status(thm), theory('equality')], [c_3749, c_5277])).
% 5.55/2.15  tff(c_5366, plain, (![B_308, E_309]: (k1_enumset1(B_308, B_308, E_309)=k2_tarski(E_309, B_308))), inference(superposition, [status(thm), theory('equality')], [c_5297, c_72])).
% 5.55/2.15  tff(c_5443, plain, (![E_310, B_311]: (k2_tarski(E_310, B_311)=k2_tarski(B_311, E_310))), inference(superposition, [status(thm), theory('equality')], [c_5366, c_70])).
% 5.55/2.15  tff(c_44, plain, (![D_29, B_25, A_24]: (D_29=B_25 | D_29=A_24 | ~r2_hidden(D_29, k2_tarski(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.55/2.15  tff(c_5509, plain, (![D_29, B_311, E_310]: (D_29=B_311 | E_310=D_29 | ~r2_hidden(D_29, k2_tarski(B_311, E_310)))), inference(superposition, [status(thm), theory('equality')], [c_5443, c_44])).
% 5.55/2.15  tff(c_6041, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6020, c_5509])).
% 5.55/2.15  tff(c_6048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_86, c_6041])).
% 5.55/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.15  
% 5.55/2.15  Inference rules
% 5.55/2.15  ----------------------
% 5.55/2.15  #Ref     : 0
% 5.55/2.15  #Sup     : 1435
% 5.55/2.15  #Fact    : 0
% 5.55/2.15  #Define  : 0
% 5.55/2.15  #Split   : 0
% 5.55/2.15  #Chain   : 0
% 5.55/2.15  #Close   : 0
% 5.55/2.15  
% 5.55/2.15  Ordering : KBO
% 5.55/2.15  
% 5.55/2.15  Simplification rules
% 5.55/2.15  ----------------------
% 5.55/2.15  #Subsume      : 98
% 5.55/2.15  #Demod        : 1980
% 5.55/2.15  #Tautology    : 1184
% 5.55/2.15  #SimpNegUnit  : 1
% 5.55/2.15  #BackRed      : 4
% 5.55/2.15  
% 5.55/2.15  #Partial instantiations: 0
% 5.55/2.15  #Strategies tried      : 1
% 5.55/2.15  
% 5.55/2.15  Timing (in seconds)
% 5.55/2.15  ----------------------
% 5.70/2.15  Preprocessing        : 0.35
% 5.70/2.15  Parsing              : 0.17
% 5.70/2.15  CNF conversion       : 0.03
% 5.70/2.15  Main loop            : 1.03
% 5.70/2.15  Inferencing          : 0.31
% 5.70/2.15  Reduction            : 0.50
% 5.70/2.15  Demodulation         : 0.43
% 5.70/2.15  BG Simplification    : 0.03
% 5.70/2.15  Subsumption          : 0.14
% 5.70/2.15  Abstraction          : 0.07
% 5.70/2.15  MUC search           : 0.00
% 5.70/2.15  Cooper               : 0.00
% 5.70/2.15  Total                : 1.42
% 5.70/2.15  Index Insertion      : 0.00
% 5.70/2.15  Index Deletion       : 0.00
% 5.70/2.15  Index Matching       : 0.00
% 5.70/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
