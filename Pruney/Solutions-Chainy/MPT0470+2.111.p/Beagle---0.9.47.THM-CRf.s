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
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 310 expanded)
%              Number of leaves         :   34 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  201 ( 757 expanded)
%              Number of equality atoms :   50 ( 171 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_10',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_73,plain,(
    k5_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    ! [A_123,B_124] :
      ( v1_relat_1(k3_xboole_0(A_123,B_124))
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_65,plain,(
    ! [A_10] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_62])).

tff(c_66,plain,(
    ! [A_10] : ~ v1_relat_1(A_10) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_44,plain,(
    ! [A_114,B_115] :
      ( v1_relat_1(k5_relat_1(A_114,B_115))
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ! [A_118] :
      ( k1_xboole_0 = A_118
      | r2_hidden(k4_tarski('#skF_8'(A_118),'#skF_9'(A_118)),A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [D_106,E_107,A_15,B_67] :
      ( r2_hidden(k4_tarski(D_106,'#skF_2'(D_106,E_107,k5_relat_1(A_15,B_67),A_15,B_67)),A_15)
      | ~ r2_hidden(k4_tarski(D_106,E_107),k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [D_106,E_107,A_15,B_67] :
      ( r2_hidden(k4_tarski('#skF_2'(D_106,E_107,k5_relat_1(A_15,B_67),A_15,B_67),E_107),B_67)
      | ~ r2_hidden(k4_tarski(D_106,E_107),k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k1_xboole_0
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    ! [A_146,B_147,C_148] :
      ( ~ r1_xboole_0(A_146,B_147)
      | ~ r2_hidden(C_148,B_147)
      | ~ r2_hidden(C_148,A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [C_151,B_152,A_153] :
      ( ~ r2_hidden(C_151,B_152)
      | ~ r2_hidden(C_151,A_153)
      | k4_xboole_0(A_153,B_152) != A_153 ) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_156,plain,(
    ! [A_162,B_163,A_164] :
      ( ~ r2_hidden('#skF_1'(A_162,B_163),A_164)
      | k4_xboole_0(A_164,A_162) != A_164
      | r1_xboole_0(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_159,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_167,plain,(
    ! [A_165,B_166] :
      ( k1_xboole_0 != A_165
      | r1_xboole_0(A_165,B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_159])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    ! [C_175,B_176,A_177] :
      ( ~ r2_hidden(C_175,B_176)
      | ~ r2_hidden(C_175,A_177)
      | k1_xboole_0 != A_177 ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_573,plain,(
    ! [A_260,B_262,A_261,E_259,D_258] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(D_258,E_259,k5_relat_1(A_261,B_262),A_261,B_262),E_259),A_260)
      | k1_xboole_0 != A_260
      | ~ r2_hidden(k4_tarski(D_258,E_259),k5_relat_1(A_261,B_262))
      | ~ v1_relat_1(k5_relat_1(A_261,B_262))
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(A_261) ) ),
    inference(resolution,[status(thm)],[c_40,c_210])).

tff(c_601,plain,(
    ! [B_267,D_268,E_269,A_270] :
      ( k1_xboole_0 != B_267
      | ~ r2_hidden(k4_tarski(D_268,E_269),k5_relat_1(A_270,B_267))
      | ~ v1_relat_1(k5_relat_1(A_270,B_267))
      | ~ v1_relat_1(B_267)
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_40,c_573])).

tff(c_647,plain,(
    ! [B_271,A_272] :
      ( k1_xboole_0 != B_271
      | ~ v1_relat_1(B_271)
      | ~ v1_relat_1(A_272)
      | k5_relat_1(A_272,B_271) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_272,B_271)) ) ),
    inference(resolution,[status(thm)],[c_48,c_601])).

tff(c_653,plain,(
    ! [B_273,A_274] :
      ( k1_xboole_0 != B_273
      | k5_relat_1(A_274,B_273) = k1_xboole_0
      | ~ v1_relat_1(B_273)
      | ~ v1_relat_1(A_274) ) ),
    inference(resolution,[status(thm)],[c_44,c_647])).

tff(c_667,plain,(
    ! [A_275] :
      ( k5_relat_1(A_275,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_275) ) ),
    inference(resolution,[status(thm)],[c_71,c_653])).

tff(c_681,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_667])).

tff(c_582,plain,(
    ! [B_67,D_106,E_107,A_15] :
      ( k1_xboole_0 != B_67
      | ~ r2_hidden(k4_tarski(D_106,E_107),k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(k5_relat_1(A_15,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_40,c_573])).

tff(c_687,plain,(
    ! [D_106,E_107] :
      ( ~ r2_hidden(k4_tarski(D_106,E_107),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_582])).

tff(c_756,plain,(
    ! [D_276,E_277] : ~ r2_hidden(k4_tarski(D_276,E_277),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_681,c_687])).

tff(c_776,plain,(
    ! [D_106,E_107,B_67] :
      ( ~ r2_hidden(k4_tarski(D_106,E_107),k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_756])).

tff(c_985,plain,(
    ! [D_287,E_288,B_289] :
      ( ~ r2_hidden(k4_tarski(D_287,E_288),k5_relat_1(k1_xboole_0,B_289))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_289))
      | ~ v1_relat_1(B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_776])).

tff(c_1038,plain,(
    ! [B_290] :
      ( ~ v1_relat_1(B_290)
      | k5_relat_1(k1_xboole_0,B_290) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_290)) ) ),
    inference(resolution,[status(thm)],[c_48,c_985])).

tff(c_1045,plain,(
    ! [B_115] :
      ( k5_relat_1(k1_xboole_0,B_115) = k1_xboole_0
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_1038])).

tff(c_1051,plain,(
    ! [B_291] :
      ( k5_relat_1(k1_xboole_0,B_291) = k1_xboole_0
      | ~ v1_relat_1(B_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1045])).

tff(c_1063,plain,(
    k5_relat_1(k1_xboole_0,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1051])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1063])).

tff(c_1072,plain,(
    k5_relat_1('#skF_10',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1073,plain,(
    k5_relat_1(k1_xboole_0,'#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1269,plain,(
    ! [D_344,E_345,A_346,B_347] :
      ( r2_hidden(k4_tarski(D_344,'#skF_2'(D_344,E_345,k5_relat_1(A_346,B_347),A_346,B_347)),A_346)
      | ~ r2_hidden(k4_tarski(D_344,E_345),k5_relat_1(A_346,B_347))
      | ~ v1_relat_1(k5_relat_1(A_346,B_347))
      | ~ v1_relat_1(B_347)
      | ~ v1_relat_1(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1280,plain,(
    ! [D_344,E_345] :
      ( r2_hidden(k4_tarski(D_344,'#skF_2'(D_344,E_345,k1_xboole_0,k1_xboole_0,'#skF_10')),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_344,E_345),k5_relat_1(k1_xboole_0,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_1269])).

tff(c_1286,plain,(
    ! [D_344,E_345] :
      ( r2_hidden(k4_tarski(D_344,'#skF_2'(D_344,E_345,k1_xboole_0,k1_xboole_0,'#skF_10')),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_344,E_345),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_52,c_71,c_1073,c_1073,c_1280])).

tff(c_1379,plain,(
    ! [D_368,E_369] :
      ( r2_hidden(k4_tarski(D_368,'#skF_2'(D_368,E_369,k1_xboole_0,k1_xboole_0,'#skF_10')),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_368,E_369),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_52,c_71,c_1073,c_1073,c_1280])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1088,plain,(
    ! [A_296,B_297] :
      ( k4_xboole_0(A_296,B_297) = k1_xboole_0
      | ~ r1_tarski(A_296,B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1096,plain,(
    ! [B_7] : k4_xboole_0(B_7,B_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1088])).

tff(c_1127,plain,(
    ! [A_309,B_310,C_311] :
      ( ~ r1_xboole_0(A_309,B_310)
      | ~ r2_hidden(C_311,B_310)
      | ~ r2_hidden(C_311,A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1143,plain,(
    ! [C_314,B_315,A_316] :
      ( ~ r2_hidden(C_314,B_315)
      | ~ r2_hidden(C_314,A_316)
      | k4_xboole_0(A_316,B_315) != A_316 ) ),
    inference(resolution,[status(thm)],[c_22,c_1127])).

tff(c_1161,plain,(
    ! [A_320,B_321,A_322] :
      ( ~ r2_hidden('#skF_1'(A_320,B_321),A_322)
      | k4_xboole_0(A_322,A_320) != A_322
      | r1_xboole_0(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_6,c_1143])).

tff(c_1167,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1161])).

tff(c_1172,plain,(
    ! [A_323,B_324] :
      ( k1_xboole_0 != A_323
      | r1_xboole_0(A_323,B_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_1167])).

tff(c_1208,plain,(
    ! [C_329,B_330,A_331] :
      ( ~ r2_hidden(C_329,B_330)
      | ~ r2_hidden(C_329,A_331)
      | k1_xboole_0 != A_331 ) ),
    inference(resolution,[status(thm)],[c_1172,c_2])).

tff(c_1288,plain,(
    ! [A_348,B_349,A_350] :
      ( ~ r2_hidden('#skF_1'(A_348,B_349),A_350)
      | k1_xboole_0 != A_350
      | r1_xboole_0(A_348,B_349) ) ),
    inference(resolution,[status(thm)],[c_6,c_1208])).

tff(c_1298,plain,(
    ! [B_351,A_352] :
      ( k1_xboole_0 != B_351
      | r1_xboole_0(A_352,B_351) ) ),
    inference(resolution,[status(thm)],[c_4,c_1288])).

tff(c_1304,plain,(
    ! [C_5,B_351,A_352] :
      ( ~ r2_hidden(C_5,B_351)
      | ~ r2_hidden(C_5,A_352)
      | k1_xboole_0 != B_351 ) ),
    inference(resolution,[status(thm)],[c_1298,c_2])).

tff(c_1477,plain,(
    ! [D_388,E_389,A_390] :
      ( ~ r2_hidden(k4_tarski(D_388,'#skF_2'(D_388,E_389,k1_xboole_0,k1_xboole_0,'#skF_10')),A_390)
      | ~ r2_hidden(k4_tarski(D_388,E_389),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1379,c_1304])).

tff(c_1483,plain,(
    ! [D_391,E_392] : ~ r2_hidden(k4_tarski(D_391,E_392),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1286,c_1477])).

tff(c_1491,plain,(
    ! [D_106,E_107,A_15] :
      ( ~ r2_hidden(k4_tarski(D_106,E_107),k5_relat_1(A_15,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_15,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_40,c_1483])).

tff(c_1513,plain,(
    ! [D_393,E_394,A_395] :
      ( ~ r2_hidden(k4_tarski(D_393,E_394),k5_relat_1(A_395,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_395,k1_xboole_0))
      | ~ v1_relat_1(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1491])).

tff(c_1534,plain,(
    ! [A_396] :
      ( ~ v1_relat_1(A_396)
      | k5_relat_1(A_396,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_396,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_48,c_1513])).

tff(c_1538,plain,(
    ! [A_114] :
      ( k5_relat_1(A_114,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_44,c_1534])).

tff(c_1542,plain,(
    ! [A_397] :
      ( k5_relat_1(A_397,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1538])).

tff(c_1554,plain,(
    k5_relat_1('#skF_10',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_1542])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1072,c_1554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.78  
% 3.98/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_10 > #skF_5 > #skF_7 > #skF_3 > #skF_1
% 3.98/1.78  
% 3.98/1.78  %Foreground sorts:
% 3.98/1.78  
% 3.98/1.78  
% 3.98/1.78  %Background operators:
% 3.98/1.78  
% 3.98/1.78  
% 3.98/1.78  %Foreground operators:
% 3.98/1.78  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.78  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.98/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.98/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.98/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.98/1.78  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.98/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.98/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.78  tff('#skF_10', type, '#skF_10': $i).
% 3.98/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.78  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.98/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.98/1.78  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.78  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.98/1.78  
% 4.08/1.80  tff(f_104, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.08/1.80  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.08/1.80  tff(f_89, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.08/1.80  tff(f_85, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.08/1.80  tff(f_97, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 4.08/1.80  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 4.08/1.80  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.80  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.08/1.80  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.08/1.80  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.08/1.80  tff(c_50, plain, (k5_relat_1('#skF_10', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.08/1.80  tff(c_73, plain, (k5_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 4.08/1.80  tff(c_52, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.08/1.80  tff(c_18, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.08/1.80  tff(c_62, plain, (![A_123, B_124]: (v1_relat_1(k3_xboole_0(A_123, B_124)) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.08/1.80  tff(c_65, plain, (![A_10]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_18, c_62])).
% 4.08/1.80  tff(c_66, plain, (![A_10]: (~v1_relat_1(A_10))), inference(splitLeft, [status(thm)], [c_65])).
% 4.08/1.80  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_52])).
% 4.08/1.80  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_65])).
% 4.08/1.80  tff(c_44, plain, (![A_114, B_115]: (v1_relat_1(k5_relat_1(A_114, B_115)) | ~v1_relat_1(B_115) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.80  tff(c_48, plain, (![A_118]: (k1_xboole_0=A_118 | r2_hidden(k4_tarski('#skF_8'(A_118), '#skF_9'(A_118)), A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.08/1.80  tff(c_42, plain, (![D_106, E_107, A_15, B_67]: (r2_hidden(k4_tarski(D_106, '#skF_2'(D_106, E_107, k5_relat_1(A_15, B_67), A_15, B_67)), A_15) | ~r2_hidden(k4_tarski(D_106, E_107), k5_relat_1(A_15, B_67)) | ~v1_relat_1(k5_relat_1(A_15, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.08/1.80  tff(c_40, plain, (![D_106, E_107, A_15, B_67]: (r2_hidden(k4_tarski('#skF_2'(D_106, E_107, k5_relat_1(A_15, B_67), A_15, B_67), E_107), B_67) | ~r2_hidden(k4_tarski(D_106, E_107), k5_relat_1(A_15, B_67)) | ~v1_relat_1(k5_relat_1(A_15, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.08/1.80  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.08/1.80  tff(c_80, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k1_xboole_0 | ~r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.80  tff(c_88, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_80])).
% 4.08/1.80  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_22, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.08/1.80  tff(c_118, plain, (![A_146, B_147, C_148]: (~r1_xboole_0(A_146, B_147) | ~r2_hidden(C_148, B_147) | ~r2_hidden(C_148, A_146))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_134, plain, (![C_151, B_152, A_153]: (~r2_hidden(C_151, B_152) | ~r2_hidden(C_151, A_153) | k4_xboole_0(A_153, B_152)!=A_153)), inference(resolution, [status(thm)], [c_22, c_118])).
% 4.08/1.80  tff(c_156, plain, (![A_162, B_163, A_164]: (~r2_hidden('#skF_1'(A_162, B_163), A_164) | k4_xboole_0(A_164, A_162)!=A_164 | r1_xboole_0(A_162, B_163))), inference(resolution, [status(thm)], [c_6, c_134])).
% 4.08/1.80  tff(c_159, plain, (![A_1, B_2]: (k4_xboole_0(A_1, A_1)!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_156])).
% 4.08/1.80  tff(c_167, plain, (![A_165, B_166]: (k1_xboole_0!=A_165 | r1_xboole_0(A_165, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_159])).
% 4.08/1.80  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_210, plain, (![C_175, B_176, A_177]: (~r2_hidden(C_175, B_176) | ~r2_hidden(C_175, A_177) | k1_xboole_0!=A_177)), inference(resolution, [status(thm)], [c_167, c_2])).
% 4.08/1.80  tff(c_573, plain, (![A_260, B_262, A_261, E_259, D_258]: (~r2_hidden(k4_tarski('#skF_2'(D_258, E_259, k5_relat_1(A_261, B_262), A_261, B_262), E_259), A_260) | k1_xboole_0!=A_260 | ~r2_hidden(k4_tarski(D_258, E_259), k5_relat_1(A_261, B_262)) | ~v1_relat_1(k5_relat_1(A_261, B_262)) | ~v1_relat_1(B_262) | ~v1_relat_1(A_261))), inference(resolution, [status(thm)], [c_40, c_210])).
% 4.08/1.80  tff(c_601, plain, (![B_267, D_268, E_269, A_270]: (k1_xboole_0!=B_267 | ~r2_hidden(k4_tarski(D_268, E_269), k5_relat_1(A_270, B_267)) | ~v1_relat_1(k5_relat_1(A_270, B_267)) | ~v1_relat_1(B_267) | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_40, c_573])).
% 4.08/1.80  tff(c_647, plain, (![B_271, A_272]: (k1_xboole_0!=B_271 | ~v1_relat_1(B_271) | ~v1_relat_1(A_272) | k5_relat_1(A_272, B_271)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_272, B_271)))), inference(resolution, [status(thm)], [c_48, c_601])).
% 4.08/1.80  tff(c_653, plain, (![B_273, A_274]: (k1_xboole_0!=B_273 | k5_relat_1(A_274, B_273)=k1_xboole_0 | ~v1_relat_1(B_273) | ~v1_relat_1(A_274))), inference(resolution, [status(thm)], [c_44, c_647])).
% 4.08/1.80  tff(c_667, plain, (![A_275]: (k5_relat_1(A_275, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_275))), inference(resolution, [status(thm)], [c_71, c_653])).
% 4.08/1.80  tff(c_681, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_667])).
% 4.08/1.80  tff(c_582, plain, (![B_67, D_106, E_107, A_15]: (k1_xboole_0!=B_67 | ~r2_hidden(k4_tarski(D_106, E_107), k5_relat_1(A_15, B_67)) | ~v1_relat_1(k5_relat_1(A_15, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_40, c_573])).
% 4.08/1.80  tff(c_687, plain, (![D_106, E_107]: (~r2_hidden(k4_tarski(D_106, E_107), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_681, c_582])).
% 4.08/1.80  tff(c_756, plain, (![D_276, E_277]: (~r2_hidden(k4_tarski(D_276, E_277), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_681, c_687])).
% 4.08/1.80  tff(c_776, plain, (![D_106, E_107, B_67]: (~r2_hidden(k4_tarski(D_106, E_107), k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_756])).
% 4.08/1.80  tff(c_985, plain, (![D_287, E_288, B_289]: (~r2_hidden(k4_tarski(D_287, E_288), k5_relat_1(k1_xboole_0, B_289)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_289)) | ~v1_relat_1(B_289))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_776])).
% 4.08/1.80  tff(c_1038, plain, (![B_290]: (~v1_relat_1(B_290) | k5_relat_1(k1_xboole_0, B_290)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_290)))), inference(resolution, [status(thm)], [c_48, c_985])).
% 4.08/1.80  tff(c_1045, plain, (![B_115]: (k5_relat_1(k1_xboole_0, B_115)=k1_xboole_0 | ~v1_relat_1(B_115) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_1038])).
% 4.08/1.80  tff(c_1051, plain, (![B_291]: (k5_relat_1(k1_xboole_0, B_291)=k1_xboole_0 | ~v1_relat_1(B_291))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1045])).
% 4.08/1.80  tff(c_1063, plain, (k5_relat_1(k1_xboole_0, '#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1051])).
% 4.08/1.80  tff(c_1071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_1063])).
% 4.08/1.80  tff(c_1072, plain, (k5_relat_1('#skF_10', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 4.08/1.80  tff(c_1073, plain, (k5_relat_1(k1_xboole_0, '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 4.08/1.80  tff(c_1269, plain, (![D_344, E_345, A_346, B_347]: (r2_hidden(k4_tarski(D_344, '#skF_2'(D_344, E_345, k5_relat_1(A_346, B_347), A_346, B_347)), A_346) | ~r2_hidden(k4_tarski(D_344, E_345), k5_relat_1(A_346, B_347)) | ~v1_relat_1(k5_relat_1(A_346, B_347)) | ~v1_relat_1(B_347) | ~v1_relat_1(A_346))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.08/1.80  tff(c_1280, plain, (![D_344, E_345]: (r2_hidden(k4_tarski(D_344, '#skF_2'(D_344, E_345, k1_xboole_0, k1_xboole_0, '#skF_10')), k1_xboole_0) | ~r2_hidden(k4_tarski(D_344, E_345), k5_relat_1(k1_xboole_0, '#skF_10')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_1269])).
% 4.08/1.80  tff(c_1286, plain, (![D_344, E_345]: (r2_hidden(k4_tarski(D_344, '#skF_2'(D_344, E_345, k1_xboole_0, k1_xboole_0, '#skF_10')), k1_xboole_0) | ~r2_hidden(k4_tarski(D_344, E_345), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_52, c_71, c_1073, c_1073, c_1280])).
% 4.08/1.80  tff(c_1379, plain, (![D_368, E_369]: (r2_hidden(k4_tarski(D_368, '#skF_2'(D_368, E_369, k1_xboole_0, k1_xboole_0, '#skF_10')), k1_xboole_0) | ~r2_hidden(k4_tarski(D_368, E_369), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_52, c_71, c_1073, c_1073, c_1280])).
% 4.08/1.80  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_1088, plain, (![A_296, B_297]: (k4_xboole_0(A_296, B_297)=k1_xboole_0 | ~r1_tarski(A_296, B_297))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.80  tff(c_1096, plain, (![B_7]: (k4_xboole_0(B_7, B_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1088])).
% 4.08/1.80  tff(c_1127, plain, (![A_309, B_310, C_311]: (~r1_xboole_0(A_309, B_310) | ~r2_hidden(C_311, B_310) | ~r2_hidden(C_311, A_309))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.08/1.80  tff(c_1143, plain, (![C_314, B_315, A_316]: (~r2_hidden(C_314, B_315) | ~r2_hidden(C_314, A_316) | k4_xboole_0(A_316, B_315)!=A_316)), inference(resolution, [status(thm)], [c_22, c_1127])).
% 4.08/1.80  tff(c_1161, plain, (![A_320, B_321, A_322]: (~r2_hidden('#skF_1'(A_320, B_321), A_322) | k4_xboole_0(A_322, A_320)!=A_322 | r1_xboole_0(A_320, B_321))), inference(resolution, [status(thm)], [c_6, c_1143])).
% 4.08/1.80  tff(c_1167, plain, (![A_1, B_2]: (k4_xboole_0(A_1, A_1)!=A_1 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_1161])).
% 4.08/1.80  tff(c_1172, plain, (![A_323, B_324]: (k1_xboole_0!=A_323 | r1_xboole_0(A_323, B_324))), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_1167])).
% 4.08/1.80  tff(c_1208, plain, (![C_329, B_330, A_331]: (~r2_hidden(C_329, B_330) | ~r2_hidden(C_329, A_331) | k1_xboole_0!=A_331)), inference(resolution, [status(thm)], [c_1172, c_2])).
% 4.08/1.80  tff(c_1288, plain, (![A_348, B_349, A_350]: (~r2_hidden('#skF_1'(A_348, B_349), A_350) | k1_xboole_0!=A_350 | r1_xboole_0(A_348, B_349))), inference(resolution, [status(thm)], [c_6, c_1208])).
% 4.08/1.80  tff(c_1298, plain, (![B_351, A_352]: (k1_xboole_0!=B_351 | r1_xboole_0(A_352, B_351))), inference(resolution, [status(thm)], [c_4, c_1288])).
% 4.08/1.80  tff(c_1304, plain, (![C_5, B_351, A_352]: (~r2_hidden(C_5, B_351) | ~r2_hidden(C_5, A_352) | k1_xboole_0!=B_351)), inference(resolution, [status(thm)], [c_1298, c_2])).
% 4.08/1.80  tff(c_1477, plain, (![D_388, E_389, A_390]: (~r2_hidden(k4_tarski(D_388, '#skF_2'(D_388, E_389, k1_xboole_0, k1_xboole_0, '#skF_10')), A_390) | ~r2_hidden(k4_tarski(D_388, E_389), k1_xboole_0))), inference(resolution, [status(thm)], [c_1379, c_1304])).
% 4.08/1.80  tff(c_1483, plain, (![D_391, E_392]: (~r2_hidden(k4_tarski(D_391, E_392), k1_xboole_0))), inference(resolution, [status(thm)], [c_1286, c_1477])).
% 4.08/1.80  tff(c_1491, plain, (![D_106, E_107, A_15]: (~r2_hidden(k4_tarski(D_106, E_107), k5_relat_1(A_15, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_15, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_40, c_1483])).
% 4.08/1.80  tff(c_1513, plain, (![D_393, E_394, A_395]: (~r2_hidden(k4_tarski(D_393, E_394), k5_relat_1(A_395, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_395, k1_xboole_0)) | ~v1_relat_1(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1491])).
% 4.08/1.80  tff(c_1534, plain, (![A_396]: (~v1_relat_1(A_396) | k5_relat_1(A_396, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_396, k1_xboole_0)))), inference(resolution, [status(thm)], [c_48, c_1513])).
% 4.08/1.80  tff(c_1538, plain, (![A_114]: (k5_relat_1(A_114, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_44, c_1534])).
% 4.08/1.80  tff(c_1542, plain, (![A_397]: (k5_relat_1(A_397, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_397))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1538])).
% 4.08/1.80  tff(c_1554, plain, (k5_relat_1('#skF_10', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_1542])).
% 4.08/1.80  tff(c_1561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1072, c_1554])).
% 4.08/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.80  
% 4.08/1.80  Inference rules
% 4.08/1.80  ----------------------
% 4.08/1.80  #Ref     : 4
% 4.08/1.80  #Sup     : 331
% 4.08/1.80  #Fact    : 0
% 4.08/1.80  #Define  : 0
% 4.08/1.80  #Split   : 3
% 4.08/1.80  #Chain   : 0
% 4.08/1.80  #Close   : 0
% 4.08/1.80  
% 4.08/1.80  Ordering : KBO
% 4.08/1.80  
% 4.08/1.80  Simplification rules
% 4.08/1.80  ----------------------
% 4.08/1.80  #Subsume      : 54
% 4.08/1.80  #Demod        : 142
% 4.08/1.80  #Tautology    : 90
% 4.08/1.80  #SimpNegUnit  : 9
% 4.08/1.80  #BackRed      : 1
% 4.08/1.80  
% 4.08/1.80  #Partial instantiations: 0
% 4.08/1.80  #Strategies tried      : 1
% 4.08/1.80  
% 4.08/1.80  Timing (in seconds)
% 4.08/1.80  ----------------------
% 4.08/1.80  Preprocessing        : 0.44
% 4.08/1.80  Parsing              : 0.26
% 4.08/1.80  CNF conversion       : 0.03
% 4.08/1.80  Main loop            : 0.54
% 4.08/1.81  Inferencing          : 0.20
% 4.08/1.81  Reduction            : 0.14
% 4.08/1.81  Demodulation         : 0.09
% 4.08/1.81  BG Simplification    : 0.03
% 4.08/1.81  Subsumption          : 0.14
% 4.08/1.81  Abstraction          : 0.03
% 4.08/1.81  MUC search           : 0.00
% 4.08/1.81  Cooper               : 0.00
% 4.08/1.81  Total                : 1.02
% 4.08/1.81  Index Insertion      : 0.00
% 4.08/1.81  Index Deletion       : 0.00
% 4.08/1.81  Index Matching       : 0.00
% 4.08/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
