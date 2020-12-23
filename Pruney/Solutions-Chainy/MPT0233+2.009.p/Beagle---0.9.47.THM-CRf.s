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
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 12.34s
% Output     : CNFRefutation 12.52s
% Verified   : 
% Statistics : Number of formulae       :  241 (3282 expanded)
%              Number of leaves         :   44 (1086 expanded)
%              Depth                    :   25
%              Number of atoms          :  277 (4865 expanded)
%              Number of equality atoms :  233 (4107 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_56,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2305,plain,(
    ! [A_200,B_201,C_202,D_203] : k2_xboole_0(k1_enumset1(A_200,B_201,C_202),k1_tarski(D_203)) = k2_enumset1(A_200,B_201,C_202,D_203) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2344,plain,(
    ! [A_41,B_42,D_203] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_203)) = k2_enumset1(A_41,A_41,B_42,D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2305])).

tff(c_25616,plain,(
    ! [A_48035,B_48036,D_48037] : k2_xboole_0(k2_tarski(A_48035,B_48036),k1_tarski(D_48037)) = k1_enumset1(A_48035,B_48036,D_48037) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2344])).

tff(c_25646,plain,(
    ! [A_40,D_48037] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_48037)) = k1_enumset1(A_40,A_40,D_48037) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_25616])).

tff(c_25733,plain,(
    ! [A_48038,D_48039] : k2_xboole_0(k1_tarski(A_48038),k1_tarski(D_48039)) = k2_tarski(A_48038,D_48039) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25646])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_68,plain,(
    ! [A_68,C_70,B_69] : k1_enumset1(A_68,C_70,B_69) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_931,plain,(
    ! [C_144,B_145,A_146] : k1_enumset1(C_144,B_145,A_146) = k1_enumset1(A_146,B_145,C_144) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1378,plain,(
    ! [C_161,B_162,A_163] : k1_enumset1(C_161,B_162,A_163) = k1_enumset1(A_163,C_161,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_931])).

tff(c_1495,plain,(
    ! [C_70,A_68,B_69] : k1_enumset1(C_70,A_68,B_69) = k1_enumset1(A_68,C_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1378])).

tff(c_2353,plain,(
    ! [A_41,B_42,D_203] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_203)) = k1_enumset1(A_41,B_42,D_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2344])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_83] :
      ( k1_xboole_0 = A_83
      | ~ r1_tarski(A_83,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_902,plain,(
    ! [A_142,B_143] : k5_xboole_0(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_923,plain,(
    ! [B_10] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_902])).

tff(c_1026,plain,(
    ! [B_147] : k4_xboole_0(k1_xboole_0,B_147) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_923])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1038,plain,(
    ! [B_147] : k5_xboole_0(B_147,k1_xboole_0) = k2_xboole_0(B_147,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_22])).

tff(c_1048,plain,(
    ! [B_147] : k2_xboole_0(B_147,k1_xboole_0) = B_147 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1038])).

tff(c_159,plain,(
    ! [B_87,A_88] : k3_xboole_0(B_87,A_88) = k3_xboole_0(A_88,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_175,plain,(
    ! [B_87] : k3_xboole_0(B_87,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_132])).

tff(c_84,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3653,plain,(
    ! [B_232,C_233,A_234] :
      ( k2_tarski(B_232,C_233) = A_234
      | k1_tarski(C_233) = A_234
      | k1_tarski(B_232) = A_234
      | k1_xboole_0 = A_234
      | ~ r1_tarski(A_234,k2_tarski(B_232,C_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3729,plain,
    ( k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_3653])).

tff(c_3968,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3729])).

tff(c_74,plain,(
    ! [C_73,B_72] : r1_tarski(k1_tarski(C_73),k2_tarski(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_362,plain,(
    ! [A_111,B_112] :
      ( k3_xboole_0(A_111,B_112) = A_111
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_384,plain,(
    ! [C_73,B_72] : k3_xboole_0(k1_tarski(C_73),k2_tarski(B_72,C_73)) = k1_tarski(C_73) ),
    inference(resolution,[status(thm)],[c_74,c_362])).

tff(c_4001,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3968,c_384])).

tff(c_4018,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_4001])).

tff(c_7226,plain,(
    ! [A_335,B_336,D_337] : k2_xboole_0(k2_tarski(A_335,B_336),k1_tarski(D_337)) = k1_enumset1(A_335,B_336,D_337) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2344])).

tff(c_7241,plain,(
    ! [A_335,B_336] : k2_xboole_0(k2_tarski(A_335,B_336),k1_xboole_0) = k1_enumset1(A_335,B_336,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4018,c_7226])).

tff(c_9797,plain,(
    ! [A_389,B_390] : k1_enumset1(A_389,B_390,'#skF_4') = k2_tarski(A_389,B_390) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_7241])).

tff(c_26,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10168,plain,(
    ! [A_392,B_393] : r2_hidden('#skF_4',k2_tarski(A_392,B_393)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_26])).

tff(c_1737,plain,(
    ! [E_177,C_178,B_179,A_180] :
      ( E_177 = C_178
      | E_177 = B_179
      | E_177 = A_180
      | ~ r2_hidden(E_177,k1_enumset1(A_180,B_179,C_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1764,plain,(
    ! [E_177,B_42,A_41] :
      ( E_177 = B_42
      | E_177 = A_41
      | E_177 = A_41
      | ~ r2_hidden(E_177,k2_tarski(A_41,B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1737])).

tff(c_10182,plain,(
    ! [B_393,A_392] :
      ( B_393 = '#skF_4'
      | A_392 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10168,c_1764])).

tff(c_10188,plain,(
    ! [A_392] : A_392 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10182])).

tff(c_10189,plain,(
    ! [A_394] : A_394 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10182])).

tff(c_10707,plain,(
    '#skF_3' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10189,c_80])).

tff(c_10720,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10188,c_10707])).

tff(c_10721,plain,(
    ! [B_393] : B_393 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10182])).

tff(c_10722,plain,(
    ! [B_7896] : B_7896 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10182])).

tff(c_11240,plain,(
    '#skF_3' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10722,c_80])).

tff(c_11253,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10721,c_11240])).

tff(c_11254,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3729])).

tff(c_11353,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11254])).

tff(c_13876,plain,(
    ! [A_15404,B_15405,D_15406] : k2_xboole_0(k2_tarski(A_15404,B_15405),k1_tarski(D_15406)) = k1_enumset1(A_15404,B_15405,D_15406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2344])).

tff(c_13891,plain,(
    ! [D_15406] : k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski(D_15406)) = k1_enumset1('#skF_5','#skF_6',D_15406) ),
    inference(superposition,[status(thm),theory(equality)],[c_11353,c_13876])).

tff(c_13936,plain,(
    ! [D_15409] : k1_enumset1('#skF_6','#skF_5',D_15409) = k1_enumset1('#skF_4','#skF_3',D_15409) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_2353,c_1495,c_13891])).

tff(c_30,plain,(
    ! [E_28,B_23,C_24] : r2_hidden(E_28,k1_enumset1(E_28,B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14019,plain,(
    ! [D_15410] : r2_hidden('#skF_6',k1_enumset1('#skF_4','#skF_3',D_15410)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13936,c_30])).

tff(c_24,plain,(
    ! [E_28,C_24,B_23,A_22] :
      ( E_28 = C_24
      | E_28 = B_23
      | E_28 = A_22
      | ~ r2_hidden(E_28,k1_enumset1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14022,plain,(
    ! [D_15410] :
      ( D_15410 = '#skF_6'
      | '#skF_6' = '#skF_3'
      | '#skF_6' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_14019,c_24])).

tff(c_14053,plain,(
    ! [D_15410] :
      ( D_15410 = '#skF_6'
      | '#skF_6' = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_14022])).

tff(c_14057,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14053])).

tff(c_14070,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14057,c_80])).

tff(c_13900,plain,(
    ! [A_40,D_15406] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_15406)) = k1_enumset1(A_40,A_40,D_15406) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_13876])).

tff(c_13904,plain,(
    ! [A_40,D_15406] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_15406)) = k2_tarski(A_40,D_15406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13900])).

tff(c_11255,plain,(
    k2_tarski('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3729])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    ! [E_28,A_22,C_24] : r2_hidden(E_28,k1_enumset1(A_22,E_28,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14084,plain,(
    ! [D_15411] : r2_hidden('#skF_5',k1_enumset1('#skF_4','#skF_3',D_15411)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13936,c_28])).

tff(c_14087,plain,(
    ! [D_15411] :
      ( D_15411 = '#skF_5'
      | '#skF_5' = '#skF_3'
      | '#skF_5' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_14084,c_24])).

tff(c_14118,plain,(
    ! [D_15411] :
      ( D_15411 = '#skF_5'
      | '#skF_5' = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_14087])).

tff(c_14122,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14118])).

tff(c_389,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_362])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_400,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(A_115,B_116)
      | ~ r1_tarski(A_115,k3_xboole_0(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_468,plain,(
    ! [B_122,C_123,B_124] : r1_tarski(k3_xboole_0(k3_xboole_0(B_122,C_123),B_124),B_122) ),
    inference(resolution,[status(thm)],[c_10,c_400])).

tff(c_582,plain,(
    ! [B_128,A_129,B_130] : r1_tarski(k3_xboole_0(k3_xboole_0(B_128,A_129),B_130),A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_468])).

tff(c_669,plain,(
    ! [A_131,B_132,A_133] : r1_tarski(k3_xboole_0(A_131,k3_xboole_0(B_132,A_133)),A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_582])).

tff(c_686,plain,(
    ! [A_131] : r1_tarski(k3_xboole_0(A_131,k2_tarski('#skF_3','#skF_4')),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_669])).

tff(c_3716,plain,(
    ! [A_131] :
      ( k3_xboole_0(A_131,k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_5','#skF_6')
      | k3_xboole_0(A_131,k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_6')
      | k3_xboole_0(A_131,k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_5')
      | k3_xboole_0(A_131,k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_686,c_3653])).

tff(c_14468,plain,(
    ! [A_15416] :
      ( k3_xboole_0(A_15416,k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_4')
      | k3_xboole_0(A_15416,k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_4')
      | k3_xboole_0(A_15416,k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_4')
      | k3_xboole_0(A_15416,k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14122,c_14057,c_54,c_14122,c_14057,c_3716])).

tff(c_14769,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_4')
    | k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_3','#skF_4')) = k1_tarski('#skF_4')
    | k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_14468])).

tff(c_14802,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_14769])).

tff(c_14803,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_11255,c_14802])).

tff(c_14905,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14803])).

tff(c_14911,plain,(
    ! [D_203] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_203)) = k1_enumset1('#skF_3','#skF_4',D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_14905,c_2353])).

tff(c_16310,plain,(
    ! [D_15454] : k1_enumset1('#skF_4','#skF_3',D_15454) = k2_tarski('#skF_4',D_15454) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13904,c_1495,c_14911])).

tff(c_16403,plain,(
    ! [D_15455] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_15455)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16310,c_28])).

tff(c_16406,plain,(
    ! [D_15455] :
      ( D_15455 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16403,c_1764])).

tff(c_16418,plain,(
    ! [D_15456] : D_15456 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14070,c_14070,c_16406])).

tff(c_16548,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16418,c_14122])).

tff(c_16900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14070,c_16548])).

tff(c_16902,plain,(
    k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14803])).

tff(c_14069,plain,(
    k2_tarski('#skF_5','#skF_4') = k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14057,c_11353])).

tff(c_16954,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14122,c_14069])).

tff(c_16955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16902,c_16954])).

tff(c_16958,plain,(
    ! [D_21908] : D_21908 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14118])).

tff(c_17416,plain,(
    ! [D_21908] : D_21908 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16958,c_82])).

tff(c_17454,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17416])).

tff(c_17458,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14053])).

tff(c_17455,plain,(
    ! [D_15410] : D_15410 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_14053])).

tff(c_18001,plain,(
    ! [D_33766] : D_33766 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17458,c_17455])).

tff(c_17456,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14053])).

tff(c_18503,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_18001,c_17456])).

tff(c_18504,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_11254])).

tff(c_18570,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18504])).

tff(c_18505,plain,(
    k2_tarski('#skF_5','#skF_6') != k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_11254])).

tff(c_18571,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18570,c_18505])).

tff(c_914,plain,(
    ! [B_87] : k5_xboole_0(B_87,k1_xboole_0) = k4_xboole_0(B_87,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_902])).

tff(c_1051,plain,(
    ! [B_148] : k4_xboole_0(B_148,k1_xboole_0) = B_148 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_914])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1061,plain,(
    ! [B_148] : k4_xboole_0(B_148,B_148) = k3_xboole_0(B_148,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_18])).

tff(c_1164,plain,(
    ! [B_152] : k4_xboole_0(B_152,B_152) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1061])).

tff(c_1179,plain,(
    ! [B_152] : k5_xboole_0(B_152,k1_xboole_0) = k2_xboole_0(B_152,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_22])).

tff(c_1193,plain,(
    ! [B_152] : k2_xboole_0(B_152,B_152) = B_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1179])).

tff(c_21616,plain,(
    ! [A_40151,B_40152,D_40153] : k2_xboole_0(k2_tarski(A_40151,B_40152),k1_tarski(D_40153)) = k1_enumset1(A_40151,B_40152,D_40153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2344])).

tff(c_21646,plain,(
    ! [A_40,D_40153] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_40153)) = k1_enumset1(A_40,A_40,D_40153) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_21616])).

tff(c_22131,plain,(
    ! [A_40161,D_40162] : k2_xboole_0(k1_tarski(A_40161),k1_tarski(D_40162)) = k2_tarski(A_40161,D_40162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21646])).

tff(c_1074,plain,(
    ! [B_148] : k4_xboole_0(B_148,B_148) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1061])).

tff(c_926,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_902])).

tff(c_1235,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_926])).

tff(c_76,plain,(
    ! [B_72,C_73] : r1_tarski(k1_tarski(B_72),k2_tarski(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1678,plain,(
    ! [B_175,C_176] : k3_xboole_0(k1_tarski(B_175),k2_tarski(B_175,C_176)) = k1_tarski(B_175) ),
    inference(resolution,[status(thm)],[c_76,c_362])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1695,plain,(
    ! [B_175,C_176] : k5_xboole_0(k1_tarski(B_175),k1_tarski(B_175)) = k4_xboole_0(k1_tarski(B_175),k2_tarski(B_175,C_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_8])).

tff(c_1729,plain,(
    ! [B_175,C_176] : k4_xboole_0(k1_tarski(B_175),k2_tarski(B_175,C_176)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_1695])).

tff(c_18595,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18570,c_1729])).

tff(c_18636,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18595,c_22])).

tff(c_18640,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_3')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18636])).

tff(c_22146,plain,(
    k2_tarski('#skF_5','#skF_3') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22131,c_18640])).

tff(c_21652,plain,(
    ! [A_40,D_40153] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_40153)) = k2_tarski(A_40,D_40153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_21646])).

tff(c_22262,plain,(
    ! [D_203] : k2_xboole_0(k1_tarski('#skF_5'),k1_tarski(D_203)) = k1_enumset1('#skF_5','#skF_3',D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_22146,c_2353])).

tff(c_22803,plain,(
    ! [D_40167] : k1_enumset1('#skF_3','#skF_5',D_40167) = k2_tarski('#skF_5',D_40167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21652,c_1495,c_22262])).

tff(c_22888,plain,(
    ! [D_40168] : r2_hidden('#skF_3',k2_tarski('#skF_5',D_40168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22803,c_30])).

tff(c_22891,plain,(
    ! [D_40168] :
      ( D_40168 = '#skF_3'
      | '#skF_5' = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_22888,c_1764])).

tff(c_22971,plain,(
    ! [D_40173] : D_40173 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_82,c_22891])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1874,plain,(
    ! [A_186,B_187] : k3_xboole_0(k3_xboole_0(A_186,B_187),A_186) = k3_xboole_0(A_186,B_187) ),
    inference(resolution,[status(thm)],[c_10,c_362])).

tff(c_1893,plain,(
    ! [A_186,B_187] : k5_xboole_0(k3_xboole_0(A_186,B_187),k3_xboole_0(A_186,B_187)) = k4_xboole_0(k3_xboole_0(A_186,B_187),A_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_8])).

tff(c_2054,plain,(
    ! [A_192,B_193] : k4_xboole_0(k3_xboole_0(A_192,B_193),A_192) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_1893])).

tff(c_2166,plain,(
    ! [B_196,A_197] : k4_xboole_0(k3_xboole_0(B_196,A_197),A_197) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2054])).

tff(c_2181,plain,(
    ! [A_197,B_196] : k2_xboole_0(A_197,k3_xboole_0(B_196,A_197)) = k5_xboole_0(A_197,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2166,c_22])).

tff(c_2240,plain,(
    ! [A_198,B_199] : k2_xboole_0(A_198,k3_xboole_0(B_199,A_198)) = A_198 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2181])).

tff(c_2274,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_2240])).

tff(c_2608,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2274])).

tff(c_19464,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18570,c_2608])).

tff(c_23212,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_5','#skF_3')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22971,c_19464])).

tff(c_23706,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_22146,c_23212])).

tff(c_23708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18571,c_23706])).

tff(c_23709,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_18504])).

tff(c_1542,plain,(
    ! [C_168,B_169] : k3_xboole_0(k1_tarski(C_168),k2_tarski(B_169,C_168)) = k1_tarski(C_168) ),
    inference(resolution,[status(thm)],[c_74,c_362])).

tff(c_1552,plain,(
    ! [C_168,B_169] : k5_xboole_0(k1_tarski(C_168),k1_tarski(C_168)) = k4_xboole_0(k1_tarski(C_168),k2_tarski(B_169,C_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1542,c_8])).

tff(c_1581,plain,(
    ! [C_168,B_169] : k4_xboole_0(k1_tarski(C_168),k2_tarski(B_169,C_168)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_1552])).

tff(c_23740,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_23709,c_1581])).

tff(c_23826,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_4')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23740,c_22])).

tff(c_23830,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_4')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23826])).

tff(c_25748,plain,(
    k2_tarski('#skF_6','#skF_4') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_25733,c_23830])).

tff(c_25652,plain,(
    ! [A_40,D_48037] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_48037)) = k2_tarski(A_40,D_48037) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25646])).

tff(c_25861,plain,(
    ! [D_203] : k2_xboole_0(k1_tarski('#skF_6'),k1_tarski(D_203)) = k1_enumset1('#skF_6','#skF_4',D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_25748,c_2353])).

tff(c_28287,plain,(
    ! [D_48079] : k1_enumset1('#skF_4','#skF_6',D_48079) = k2_tarski('#skF_6',D_48079) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25652,c_1495,c_25861])).

tff(c_28375,plain,(
    ! [D_48080] : r2_hidden('#skF_4',k2_tarski('#skF_6',D_48080)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28287,c_30])).

tff(c_28387,plain,(
    ! [D_48080] :
      ( D_48080 = '#skF_4'
      | '#skF_6' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_28375,c_1764])).

tff(c_28680,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28387])).

tff(c_1011,plain,(
    ! [B_42,A_41] : k1_enumset1(B_42,A_41,A_41) = k2_tarski(A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_931])).

tff(c_23714,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23709,c_2274])).

tff(c_25622,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_6') = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_25616,c_23714])).

tff(c_25648,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_25622])).

tff(c_23711,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23709,c_18505])).

tff(c_25657,plain,(
    k2_tarski('#skF_6','#skF_5') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25648,c_23711])).

tff(c_28695,plain,(
    k2_tarski('#skF_4','#skF_5') != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28680,c_28680,c_25657])).

tff(c_28723,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28680,c_23709])).

tff(c_28724,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28680,c_80])).

tff(c_388,plain,(
    ! [B_72,C_73] : k3_xboole_0(k1_tarski(B_72),k2_tarski(B_72,C_73)) = k1_tarski(B_72) ),
    inference(resolution,[status(thm)],[c_76,c_362])).

tff(c_23737,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_6')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23709,c_388])).

tff(c_185,plain,(
    ! [A_88,B_87] : r1_tarski(k3_xboole_0(A_88,B_87),B_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_10])).

tff(c_2873,plain,(
    ! [A_213,B_214] : k3_xboole_0(k3_xboole_0(A_213,B_214),B_214) = k3_xboole_0(A_213,B_214) ),
    inference(resolution,[status(thm)],[c_185,c_362])).

tff(c_3016,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2873])).

tff(c_23903,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23737,c_3016])).

tff(c_23978,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_23903])).

tff(c_2066,plain,(
    ! [A_192,B_193] : k2_xboole_0(A_192,k3_xboole_0(A_192,B_193)) = k5_xboole_0(A_192,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_22])).

tff(c_2103,plain,(
    ! [A_192,B_193] : k2_xboole_0(A_192,k3_xboole_0(A_192,B_193)) = A_192 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2066])).

tff(c_24352,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_3')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_23978,c_2103])).

tff(c_25745,plain,(
    k2_tarski('#skF_6','#skF_3') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_25733,c_24352])).

tff(c_25791,plain,(
    ! [D_203] : k2_xboole_0(k1_tarski('#skF_6'),k1_tarski(D_203)) = k1_enumset1('#skF_6','#skF_3',D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_25745,c_2353])).

tff(c_25840,plain,(
    ! [D_203] : k1_enumset1('#skF_3','#skF_6',D_203) = k2_tarski('#skF_6',D_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25652,c_1495,c_25791])).

tff(c_29291,plain,(
    ! [D_48092] : k1_enumset1('#skF_4','#skF_3',D_48092) = k2_tarski('#skF_4',D_48092) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28680,c_1495,c_28680,c_25840])).

tff(c_29387,plain,(
    ! [D_48093] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_48093)) ),
    inference(superposition,[status(thm),theory(equality)],[c_29291,c_28])).

tff(c_29390,plain,(
    ! [D_48093] :
      ( D_48093 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_29387,c_1764])).

tff(c_29402,plain,(
    ! [D_48094] : D_48094 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_28724,c_28724,c_29390])).

tff(c_28696,plain,(
    k2_tarski('#skF_5','#skF_4') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28680,c_28680,c_25648])).

tff(c_29424,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_29402,c_28696])).

tff(c_29856,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28723,c_29424])).

tff(c_29858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28695,c_29856])).

tff(c_29989,plain,(
    ! [D_54491] : D_54491 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28387])).

tff(c_30159,plain,(
    k2_tarski('#skF_6','#skF_4') != k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_29989,c_25657])).

tff(c_30692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25748,c_30159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.34/4.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.40/4.63  
% 12.40/4.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.40/4.63  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 12.40/4.63  
% 12.40/4.63  %Foreground sorts:
% 12.40/4.63  
% 12.40/4.63  
% 12.40/4.63  %Background operators:
% 12.40/4.63  
% 12.40/4.63  
% 12.40/4.63  %Foreground operators:
% 12.40/4.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.40/4.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.40/4.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.40/4.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.40/4.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.40/4.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.40/4.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.40/4.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.40/4.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.40/4.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.40/4.63  tff('#skF_5', type, '#skF_5': $i).
% 12.40/4.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 12.40/4.63  tff('#skF_6', type, '#skF_6': $i).
% 12.40/4.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.40/4.63  tff('#skF_3', type, '#skF_3': $i).
% 12.40/4.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.40/4.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.40/4.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.40/4.63  tff('#skF_4', type, '#skF_4': $i).
% 12.40/4.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.40/4.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.40/4.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.40/4.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.40/4.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 12.40/4.63  
% 12.52/4.66  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.52/4.66  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.52/4.66  tff(f_80, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.52/4.66  tff(f_74, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 12.52/4.66  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.52/4.66  tff(f_115, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 12.52/4.66  tff(f_90, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 12.52/4.66  tff(f_70, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 12.52/4.66  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.52/4.66  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.52/4.66  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.52/4.66  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.52/4.66  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.52/4.66  tff(f_105, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 12.52/4.66  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.52/4.66  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 12.52/4.66  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.52/4.66  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 12.52/4.66  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.52/4.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.52/4.66  tff(c_56, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.52/4.66  tff(c_54, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.52/4.66  tff(c_58, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.52/4.66  tff(c_2305, plain, (![A_200, B_201, C_202, D_203]: (k2_xboole_0(k1_enumset1(A_200, B_201, C_202), k1_tarski(D_203))=k2_enumset1(A_200, B_201, C_202, D_203))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.52/4.66  tff(c_2344, plain, (![A_41, B_42, D_203]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_203))=k2_enumset1(A_41, A_41, B_42, D_203))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2305])).
% 12.52/4.66  tff(c_25616, plain, (![A_48035, B_48036, D_48037]: (k2_xboole_0(k2_tarski(A_48035, B_48036), k1_tarski(D_48037))=k1_enumset1(A_48035, B_48036, D_48037))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2344])).
% 12.52/4.66  tff(c_25646, plain, (![A_40, D_48037]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_48037))=k1_enumset1(A_40, A_40, D_48037))), inference(superposition, [status(thm), theory('equality')], [c_54, c_25616])).
% 12.52/4.66  tff(c_25733, plain, (![A_48038, D_48039]: (k2_xboole_0(k1_tarski(A_48038), k1_tarski(D_48039))=k2_tarski(A_48038, D_48039))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_25646])).
% 12.52/4.66  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.52/4.66  tff(c_80, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.52/4.66  tff(c_68, plain, (![A_68, C_70, B_69]: (k1_enumset1(A_68, C_70, B_69)=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.52/4.66  tff(c_931, plain, (![C_144, B_145, A_146]: (k1_enumset1(C_144, B_145, A_146)=k1_enumset1(A_146, B_145, C_144))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.52/4.66  tff(c_1378, plain, (![C_161, B_162, A_163]: (k1_enumset1(C_161, B_162, A_163)=k1_enumset1(A_163, C_161, B_162))), inference(superposition, [status(thm), theory('equality')], [c_68, c_931])).
% 12.52/4.66  tff(c_1495, plain, (![C_70, A_68, B_69]: (k1_enumset1(C_70, A_68, B_69)=k1_enumset1(A_68, C_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1378])).
% 12.52/4.66  tff(c_2353, plain, (![A_41, B_42, D_203]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_203))=k1_enumset1(A_41, B_42, D_203))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2344])).
% 12.52/4.66  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.52/4.66  tff(c_121, plain, (![A_83]: (k1_xboole_0=A_83 | ~r1_tarski(A_83, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.52/4.66  tff(c_132, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_121])).
% 12.52/4.66  tff(c_902, plain, (![A_142, B_143]: (k5_xboole_0(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.52/4.66  tff(c_923, plain, (![B_10]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_10))), inference(superposition, [status(thm), theory('equality')], [c_132, c_902])).
% 12.52/4.66  tff(c_1026, plain, (![B_147]: (k4_xboole_0(k1_xboole_0, B_147)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_923])).
% 12.52/4.66  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.52/4.66  tff(c_1038, plain, (![B_147]: (k5_xboole_0(B_147, k1_xboole_0)=k2_xboole_0(B_147, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1026, c_22])).
% 12.52/4.66  tff(c_1048, plain, (![B_147]: (k2_xboole_0(B_147, k1_xboole_0)=B_147)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1038])).
% 12.52/4.66  tff(c_159, plain, (![B_87, A_88]: (k3_xboole_0(B_87, A_88)=k3_xboole_0(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.52/4.66  tff(c_175, plain, (![B_87]: (k3_xboole_0(B_87, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_159, c_132])).
% 12.52/4.66  tff(c_84, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.52/4.66  tff(c_3653, plain, (![B_232, C_233, A_234]: (k2_tarski(B_232, C_233)=A_234 | k1_tarski(C_233)=A_234 | k1_tarski(B_232)=A_234 | k1_xboole_0=A_234 | ~r1_tarski(A_234, k2_tarski(B_232, C_233)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.52/4.66  tff(c_3729, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_3653])).
% 12.52/4.66  tff(c_3968, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3729])).
% 12.52/4.66  tff(c_74, plain, (![C_73, B_72]: (r1_tarski(k1_tarski(C_73), k2_tarski(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.52/4.66  tff(c_362, plain, (![A_111, B_112]: (k3_xboole_0(A_111, B_112)=A_111 | ~r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.52/4.66  tff(c_384, plain, (![C_73, B_72]: (k3_xboole_0(k1_tarski(C_73), k2_tarski(B_72, C_73))=k1_tarski(C_73))), inference(resolution, [status(thm)], [c_74, c_362])).
% 12.52/4.66  tff(c_4001, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3968, c_384])).
% 12.52/4.66  tff(c_4018, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_175, c_4001])).
% 12.52/4.66  tff(c_7226, plain, (![A_335, B_336, D_337]: (k2_xboole_0(k2_tarski(A_335, B_336), k1_tarski(D_337))=k1_enumset1(A_335, B_336, D_337))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2344])).
% 12.52/4.66  tff(c_7241, plain, (![A_335, B_336]: (k2_xboole_0(k2_tarski(A_335, B_336), k1_xboole_0)=k1_enumset1(A_335, B_336, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4018, c_7226])).
% 12.52/4.66  tff(c_9797, plain, (![A_389, B_390]: (k1_enumset1(A_389, B_390, '#skF_4')=k2_tarski(A_389, B_390))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_7241])).
% 12.52/4.66  tff(c_26, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.52/4.66  tff(c_10168, plain, (![A_392, B_393]: (r2_hidden('#skF_4', k2_tarski(A_392, B_393)))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_26])).
% 12.52/4.66  tff(c_1737, plain, (![E_177, C_178, B_179, A_180]: (E_177=C_178 | E_177=B_179 | E_177=A_180 | ~r2_hidden(E_177, k1_enumset1(A_180, B_179, C_178)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.52/4.66  tff(c_1764, plain, (![E_177, B_42, A_41]: (E_177=B_42 | E_177=A_41 | E_177=A_41 | ~r2_hidden(E_177, k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1737])).
% 12.52/4.66  tff(c_10182, plain, (![B_393, A_392]: (B_393='#skF_4' | A_392='#skF_4')), inference(resolution, [status(thm)], [c_10168, c_1764])).
% 12.52/4.66  tff(c_10188, plain, (![A_392]: (A_392='#skF_4')), inference(splitLeft, [status(thm)], [c_10182])).
% 12.52/4.66  tff(c_10189, plain, (![A_394]: (A_394='#skF_4')), inference(splitLeft, [status(thm)], [c_10182])).
% 12.52/4.66  tff(c_10707, plain, ('#skF_3'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10189, c_80])).
% 12.52/4.66  tff(c_10720, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10188, c_10707])).
% 12.52/4.66  tff(c_10721, plain, (![B_393]: (B_393='#skF_4')), inference(splitRight, [status(thm)], [c_10182])).
% 12.52/4.66  tff(c_10722, plain, (![B_7896]: (B_7896='#skF_4')), inference(splitRight, [status(thm)], [c_10182])).
% 12.52/4.66  tff(c_11240, plain, ('#skF_3'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10722, c_80])).
% 12.52/4.66  tff(c_11253, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10721, c_11240])).
% 12.52/4.66  tff(c_11254, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_3729])).
% 12.52/4.66  tff(c_11353, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_11254])).
% 12.52/4.66  tff(c_13876, plain, (![A_15404, B_15405, D_15406]: (k2_xboole_0(k2_tarski(A_15404, B_15405), k1_tarski(D_15406))=k1_enumset1(A_15404, B_15405, D_15406))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2344])).
% 12.52/4.66  tff(c_13891, plain, (![D_15406]: (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski(D_15406))=k1_enumset1('#skF_5', '#skF_6', D_15406))), inference(superposition, [status(thm), theory('equality')], [c_11353, c_13876])).
% 12.52/4.66  tff(c_13936, plain, (![D_15409]: (k1_enumset1('#skF_6', '#skF_5', D_15409)=k1_enumset1('#skF_4', '#skF_3', D_15409))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_2353, c_1495, c_13891])).
% 12.52/4.66  tff(c_30, plain, (![E_28, B_23, C_24]: (r2_hidden(E_28, k1_enumset1(E_28, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.52/4.66  tff(c_14019, plain, (![D_15410]: (r2_hidden('#skF_6', k1_enumset1('#skF_4', '#skF_3', D_15410)))), inference(superposition, [status(thm), theory('equality')], [c_13936, c_30])).
% 12.52/4.66  tff(c_24, plain, (![E_28, C_24, B_23, A_22]: (E_28=C_24 | E_28=B_23 | E_28=A_22 | ~r2_hidden(E_28, k1_enumset1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.52/4.66  tff(c_14022, plain, (![D_15410]: (D_15410='#skF_6' | '#skF_6'='#skF_3' | '#skF_6'='#skF_4')), inference(resolution, [status(thm)], [c_14019, c_24])).
% 12.52/4.66  tff(c_14053, plain, (![D_15410]: (D_15410='#skF_6' | '#skF_6'='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_14022])).
% 12.52/4.66  tff(c_14057, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_14053])).
% 12.52/4.66  tff(c_14070, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14057, c_80])).
% 12.52/4.66  tff(c_13900, plain, (![A_40, D_15406]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_15406))=k1_enumset1(A_40, A_40, D_15406))), inference(superposition, [status(thm), theory('equality')], [c_54, c_13876])).
% 12.52/4.66  tff(c_13904, plain, (![A_40, D_15406]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_15406))=k2_tarski(A_40, D_15406))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13900])).
% 12.52/4.66  tff(c_11255, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3729])).
% 12.52/4.66  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.52/4.66  tff(c_82, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.52/4.66  tff(c_28, plain, (![E_28, A_22, C_24]: (r2_hidden(E_28, k1_enumset1(A_22, E_28, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.52/4.66  tff(c_14084, plain, (![D_15411]: (r2_hidden('#skF_5', k1_enumset1('#skF_4', '#skF_3', D_15411)))), inference(superposition, [status(thm), theory('equality')], [c_13936, c_28])).
% 12.52/4.66  tff(c_14087, plain, (![D_15411]: (D_15411='#skF_5' | '#skF_5'='#skF_3' | '#skF_5'='#skF_4')), inference(resolution, [status(thm)], [c_14084, c_24])).
% 12.52/4.66  tff(c_14118, plain, (![D_15411]: (D_15411='#skF_5' | '#skF_5'='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_14087])).
% 12.52/4.66  tff(c_14122, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_14118])).
% 12.52/4.66  tff(c_389, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_362])).
% 12.52/4.66  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.52/4.66  tff(c_400, plain, (![A_115, B_116, C_117]: (r1_tarski(A_115, B_116) | ~r1_tarski(A_115, k3_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.52/4.66  tff(c_468, plain, (![B_122, C_123, B_124]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_122, C_123), B_124), B_122))), inference(resolution, [status(thm)], [c_10, c_400])).
% 12.52/4.66  tff(c_582, plain, (![B_128, A_129, B_130]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_128, A_129), B_130), A_129))), inference(superposition, [status(thm), theory('equality')], [c_4, c_468])).
% 12.52/4.66  tff(c_669, plain, (![A_131, B_132, A_133]: (r1_tarski(k3_xboole_0(A_131, k3_xboole_0(B_132, A_133)), A_133))), inference(superposition, [status(thm), theory('equality')], [c_4, c_582])).
% 12.52/4.66  tff(c_686, plain, (![A_131]: (r1_tarski(k3_xboole_0(A_131, k2_tarski('#skF_3', '#skF_4')), k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_389, c_669])).
% 12.52/4.66  tff(c_3716, plain, (![A_131]: (k3_xboole_0(A_131, k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_5', '#skF_6') | k3_xboole_0(A_131, k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_6') | k3_xboole_0(A_131, k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_5') | k3_xboole_0(A_131, k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_686, c_3653])).
% 12.52/4.66  tff(c_14468, plain, (![A_15416]: (k3_xboole_0(A_15416, k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_4') | k3_xboole_0(A_15416, k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_4') | k3_xboole_0(A_15416, k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_4') | k3_xboole_0(A_15416, k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14122, c_14057, c_54, c_14122, c_14057, c_3716])).
% 12.52/4.66  tff(c_14769, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_4') | k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_3', '#skF_4'))=k1_tarski('#skF_4') | k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6, c_14468])).
% 12.52/4.66  tff(c_14802, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_6, c_14769])).
% 12.52/4.66  tff(c_14803, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_11255, c_14802])).
% 12.52/4.66  tff(c_14905, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_14803])).
% 12.52/4.66  tff(c_14911, plain, (![D_203]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_203))=k1_enumset1('#skF_3', '#skF_4', D_203))), inference(superposition, [status(thm), theory('equality')], [c_14905, c_2353])).
% 12.52/4.66  tff(c_16310, plain, (![D_15454]: (k1_enumset1('#skF_4', '#skF_3', D_15454)=k2_tarski('#skF_4', D_15454))), inference(demodulation, [status(thm), theory('equality')], [c_13904, c_1495, c_14911])).
% 12.52/4.66  tff(c_16403, plain, (![D_15455]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_15455)))), inference(superposition, [status(thm), theory('equality')], [c_16310, c_28])).
% 12.52/4.66  tff(c_16406, plain, (![D_15455]: (D_15455='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_16403, c_1764])).
% 12.52/4.66  tff(c_16418, plain, (![D_15456]: (D_15456='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_14070, c_14070, c_16406])).
% 12.52/4.66  tff(c_16548, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16418, c_14122])).
% 12.52/4.66  tff(c_16900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14070, c_16548])).
% 12.52/4.66  tff(c_16902, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_14803])).
% 12.52/4.66  tff(c_14069, plain, (k2_tarski('#skF_5', '#skF_4')=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14057, c_11353])).
% 12.52/4.66  tff(c_16954, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14122, c_14069])).
% 12.52/4.66  tff(c_16955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16902, c_16954])).
% 12.52/4.66  tff(c_16958, plain, (![D_21908]: (D_21908='#skF_5')), inference(splitRight, [status(thm)], [c_14118])).
% 12.52/4.66  tff(c_17416, plain, (![D_21908]: (D_21908!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16958, c_82])).
% 12.52/4.66  tff(c_17454, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_17416])).
% 12.52/4.66  tff(c_17458, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_14053])).
% 12.52/4.66  tff(c_17455, plain, (![D_15410]: (D_15410='#skF_6')), inference(splitRight, [status(thm)], [c_14053])).
% 12.52/4.66  tff(c_18001, plain, (![D_33766]: (D_33766='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17458, c_17455])).
% 12.52/4.66  tff(c_17456, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_14053])).
% 12.52/4.66  tff(c_18503, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_18001, c_17456])).
% 12.52/4.66  tff(c_18504, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_11254])).
% 12.52/4.66  tff(c_18570, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_18504])).
% 12.52/4.66  tff(c_18505, plain, (k2_tarski('#skF_5', '#skF_6')!=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_11254])).
% 12.52/4.66  tff(c_18571, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18570, c_18505])).
% 12.52/4.66  tff(c_914, plain, (![B_87]: (k5_xboole_0(B_87, k1_xboole_0)=k4_xboole_0(B_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_175, c_902])).
% 12.52/4.66  tff(c_1051, plain, (![B_148]: (k4_xboole_0(B_148, k1_xboole_0)=B_148)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_914])).
% 12.52/4.66  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.52/4.66  tff(c_1061, plain, (![B_148]: (k4_xboole_0(B_148, B_148)=k3_xboole_0(B_148, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1051, c_18])).
% 12.52/4.66  tff(c_1164, plain, (![B_152]: (k4_xboole_0(B_152, B_152)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_1061])).
% 12.52/4.66  tff(c_1179, plain, (![B_152]: (k5_xboole_0(B_152, k1_xboole_0)=k2_xboole_0(B_152, B_152))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_22])).
% 12.52/4.66  tff(c_1193, plain, (![B_152]: (k2_xboole_0(B_152, B_152)=B_152)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1179])).
% 12.52/4.66  tff(c_21616, plain, (![A_40151, B_40152, D_40153]: (k2_xboole_0(k2_tarski(A_40151, B_40152), k1_tarski(D_40153))=k1_enumset1(A_40151, B_40152, D_40153))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2344])).
% 12.52/4.66  tff(c_21646, plain, (![A_40, D_40153]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_40153))=k1_enumset1(A_40, A_40, D_40153))), inference(superposition, [status(thm), theory('equality')], [c_54, c_21616])).
% 12.52/4.66  tff(c_22131, plain, (![A_40161, D_40162]: (k2_xboole_0(k1_tarski(A_40161), k1_tarski(D_40162))=k2_tarski(A_40161, D_40162))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_21646])).
% 12.52/4.66  tff(c_1074, plain, (![B_148]: (k4_xboole_0(B_148, B_148)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_1061])).
% 12.52/4.66  tff(c_926, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_902])).
% 12.52/4.66  tff(c_1235, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_926])).
% 12.52/4.66  tff(c_76, plain, (![B_72, C_73]: (r1_tarski(k1_tarski(B_72), k2_tarski(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.52/4.66  tff(c_1678, plain, (![B_175, C_176]: (k3_xboole_0(k1_tarski(B_175), k2_tarski(B_175, C_176))=k1_tarski(B_175))), inference(resolution, [status(thm)], [c_76, c_362])).
% 12.52/4.66  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.52/4.66  tff(c_1695, plain, (![B_175, C_176]: (k5_xboole_0(k1_tarski(B_175), k1_tarski(B_175))=k4_xboole_0(k1_tarski(B_175), k2_tarski(B_175, C_176)))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_8])).
% 12.52/4.66  tff(c_1729, plain, (![B_175, C_176]: (k4_xboole_0(k1_tarski(B_175), k2_tarski(B_175, C_176))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_1695])).
% 12.52/4.66  tff(c_18595, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18570, c_1729])).
% 12.52/4.66  tff(c_18636, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18595, c_22])).
% 12.52/4.66  tff(c_18640, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_3'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18636])).
% 12.52/4.66  tff(c_22146, plain, (k2_tarski('#skF_5', '#skF_3')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22131, c_18640])).
% 12.52/4.66  tff(c_21652, plain, (![A_40, D_40153]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_40153))=k2_tarski(A_40, D_40153))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_21646])).
% 12.52/4.66  tff(c_22262, plain, (![D_203]: (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski(D_203))=k1_enumset1('#skF_5', '#skF_3', D_203))), inference(superposition, [status(thm), theory('equality')], [c_22146, c_2353])).
% 12.52/4.66  tff(c_22803, plain, (![D_40167]: (k1_enumset1('#skF_3', '#skF_5', D_40167)=k2_tarski('#skF_5', D_40167))), inference(demodulation, [status(thm), theory('equality')], [c_21652, c_1495, c_22262])).
% 12.52/4.66  tff(c_22888, plain, (![D_40168]: (r2_hidden('#skF_3', k2_tarski('#skF_5', D_40168)))), inference(superposition, [status(thm), theory('equality')], [c_22803, c_30])).
% 12.52/4.66  tff(c_22891, plain, (![D_40168]: (D_40168='#skF_3' | '#skF_5'='#skF_3')), inference(resolution, [status(thm)], [c_22888, c_1764])).
% 12.52/4.66  tff(c_22971, plain, (![D_40173]: (D_40173='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_82, c_22891])).
% 12.52/4.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.52/4.66  tff(c_1874, plain, (![A_186, B_187]: (k3_xboole_0(k3_xboole_0(A_186, B_187), A_186)=k3_xboole_0(A_186, B_187))), inference(resolution, [status(thm)], [c_10, c_362])).
% 12.52/4.66  tff(c_1893, plain, (![A_186, B_187]: (k5_xboole_0(k3_xboole_0(A_186, B_187), k3_xboole_0(A_186, B_187))=k4_xboole_0(k3_xboole_0(A_186, B_187), A_186))), inference(superposition, [status(thm), theory('equality')], [c_1874, c_8])).
% 12.52/4.66  tff(c_2054, plain, (![A_192, B_193]: (k4_xboole_0(k3_xboole_0(A_192, B_193), A_192)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_1893])).
% 12.52/4.66  tff(c_2166, plain, (![B_196, A_197]: (k4_xboole_0(k3_xboole_0(B_196, A_197), A_197)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2054])).
% 12.52/4.66  tff(c_2181, plain, (![A_197, B_196]: (k2_xboole_0(A_197, k3_xboole_0(B_196, A_197))=k5_xboole_0(A_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2166, c_22])).
% 12.52/4.66  tff(c_2240, plain, (![A_198, B_199]: (k2_xboole_0(A_198, k3_xboole_0(B_199, A_198))=A_198)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2181])).
% 12.52/4.66  tff(c_2274, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_389, c_2240])).
% 12.52/4.66  tff(c_2608, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2, c_2274])).
% 12.52/4.66  tff(c_19464, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18570, c_2608])).
% 12.52/4.66  tff(c_23212, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_5', '#skF_3'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22971, c_19464])).
% 12.52/4.66  tff(c_23706, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_22146, c_23212])).
% 12.52/4.66  tff(c_23708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18571, c_23706])).
% 12.52/4.66  tff(c_23709, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_18504])).
% 12.52/4.66  tff(c_1542, plain, (![C_168, B_169]: (k3_xboole_0(k1_tarski(C_168), k2_tarski(B_169, C_168))=k1_tarski(C_168))), inference(resolution, [status(thm)], [c_74, c_362])).
% 12.52/4.66  tff(c_1552, plain, (![C_168, B_169]: (k5_xboole_0(k1_tarski(C_168), k1_tarski(C_168))=k4_xboole_0(k1_tarski(C_168), k2_tarski(B_169, C_168)))), inference(superposition, [status(thm), theory('equality')], [c_1542, c_8])).
% 12.52/4.66  tff(c_1581, plain, (![C_168, B_169]: (k4_xboole_0(k1_tarski(C_168), k2_tarski(B_169, C_168))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_1552])).
% 12.52/4.66  tff(c_23740, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_23709, c_1581])).
% 12.52/4.66  tff(c_23826, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_4'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_23740, c_22])).
% 12.52/4.66  tff(c_23830, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_4'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23826])).
% 12.52/4.66  tff(c_25748, plain, (k2_tarski('#skF_6', '#skF_4')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_25733, c_23830])).
% 12.52/4.66  tff(c_25652, plain, (![A_40, D_48037]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_48037))=k2_tarski(A_40, D_48037))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_25646])).
% 12.52/4.66  tff(c_25861, plain, (![D_203]: (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski(D_203))=k1_enumset1('#skF_6', '#skF_4', D_203))), inference(superposition, [status(thm), theory('equality')], [c_25748, c_2353])).
% 12.52/4.66  tff(c_28287, plain, (![D_48079]: (k1_enumset1('#skF_4', '#skF_6', D_48079)=k2_tarski('#skF_6', D_48079))), inference(demodulation, [status(thm), theory('equality')], [c_25652, c_1495, c_25861])).
% 12.52/4.66  tff(c_28375, plain, (![D_48080]: (r2_hidden('#skF_4', k2_tarski('#skF_6', D_48080)))), inference(superposition, [status(thm), theory('equality')], [c_28287, c_30])).
% 12.52/4.66  tff(c_28387, plain, (![D_48080]: (D_48080='#skF_4' | '#skF_6'='#skF_4')), inference(resolution, [status(thm)], [c_28375, c_1764])).
% 12.52/4.66  tff(c_28680, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_28387])).
% 12.52/4.66  tff(c_1011, plain, (![B_42, A_41]: (k1_enumset1(B_42, A_41, A_41)=k2_tarski(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_56, c_931])).
% 12.52/4.66  tff(c_23714, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23709, c_2274])).
% 12.52/4.66  tff(c_25622, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_6')=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_25616, c_23714])).
% 12.52/4.66  tff(c_25648, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_25622])).
% 12.52/4.66  tff(c_23711, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23709, c_18505])).
% 12.52/4.66  tff(c_25657, plain, (k2_tarski('#skF_6', '#skF_5')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25648, c_23711])).
% 12.52/4.66  tff(c_28695, plain, (k2_tarski('#skF_4', '#skF_5')!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28680, c_28680, c_25657])).
% 12.52/4.66  tff(c_28723, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28680, c_23709])).
% 12.52/4.66  tff(c_28724, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28680, c_80])).
% 12.52/4.66  tff(c_388, plain, (![B_72, C_73]: (k3_xboole_0(k1_tarski(B_72), k2_tarski(B_72, C_73))=k1_tarski(B_72))), inference(resolution, [status(thm)], [c_76, c_362])).
% 12.52/4.66  tff(c_23737, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_6'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23709, c_388])).
% 12.52/4.66  tff(c_185, plain, (![A_88, B_87]: (r1_tarski(k3_xboole_0(A_88, B_87), B_87))), inference(superposition, [status(thm), theory('equality')], [c_159, c_10])).
% 12.52/4.66  tff(c_2873, plain, (![A_213, B_214]: (k3_xboole_0(k3_xboole_0(A_213, B_214), B_214)=k3_xboole_0(A_213, B_214))), inference(resolution, [status(thm)], [c_185, c_362])).
% 12.52/4.66  tff(c_3016, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2873])).
% 12.52/4.66  tff(c_23903, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23737, c_3016])).
% 12.52/4.66  tff(c_23978, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_23903])).
% 12.52/4.66  tff(c_2066, plain, (![A_192, B_193]: (k2_xboole_0(A_192, k3_xboole_0(A_192, B_193))=k5_xboole_0(A_192, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2054, c_22])).
% 12.52/4.66  tff(c_2103, plain, (![A_192, B_193]: (k2_xboole_0(A_192, k3_xboole_0(A_192, B_193))=A_192)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2066])).
% 12.52/4.66  tff(c_24352, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_3'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_23978, c_2103])).
% 12.52/4.66  tff(c_25745, plain, (k2_tarski('#skF_6', '#skF_3')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_25733, c_24352])).
% 12.52/4.66  tff(c_25791, plain, (![D_203]: (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski(D_203))=k1_enumset1('#skF_6', '#skF_3', D_203))), inference(superposition, [status(thm), theory('equality')], [c_25745, c_2353])).
% 12.52/4.66  tff(c_25840, plain, (![D_203]: (k1_enumset1('#skF_3', '#skF_6', D_203)=k2_tarski('#skF_6', D_203))), inference(demodulation, [status(thm), theory('equality')], [c_25652, c_1495, c_25791])).
% 12.52/4.66  tff(c_29291, plain, (![D_48092]: (k1_enumset1('#skF_4', '#skF_3', D_48092)=k2_tarski('#skF_4', D_48092))), inference(demodulation, [status(thm), theory('equality')], [c_28680, c_1495, c_28680, c_25840])).
% 12.52/4.66  tff(c_29387, plain, (![D_48093]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_48093)))), inference(superposition, [status(thm), theory('equality')], [c_29291, c_28])).
% 12.52/4.66  tff(c_29390, plain, (![D_48093]: (D_48093='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_29387, c_1764])).
% 12.52/4.66  tff(c_29402, plain, (![D_48094]: (D_48094='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28724, c_28724, c_29390])).
% 12.52/4.66  tff(c_28696, plain, (k2_tarski('#skF_5', '#skF_4')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28680, c_28680, c_25648])).
% 12.52/4.66  tff(c_29424, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_29402, c_28696])).
% 12.52/4.66  tff(c_29856, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28723, c_29424])).
% 12.52/4.66  tff(c_29858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28695, c_29856])).
% 12.52/4.66  tff(c_29989, plain, (![D_54491]: (D_54491='#skF_4')), inference(splitRight, [status(thm)], [c_28387])).
% 12.52/4.66  tff(c_30159, plain, (k2_tarski('#skF_6', '#skF_4')!=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_29989, c_25657])).
% 12.52/4.66  tff(c_30692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25748, c_30159])).
% 12.52/4.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.52/4.66  
% 12.52/4.66  Inference rules
% 12.52/4.66  ----------------------
% 12.52/4.66  #Ref     : 1
% 12.52/4.66  #Sup     : 8533
% 12.52/4.66  #Fact    : 21
% 12.52/4.66  #Define  : 0
% 12.52/4.66  #Split   : 8
% 12.52/4.66  #Chain   : 0
% 12.52/4.66  #Close   : 0
% 12.52/4.66  
% 12.52/4.66  Ordering : KBO
% 12.52/4.66  
% 12.52/4.66  Simplification rules
% 12.52/4.66  ----------------------
% 12.52/4.66  #Subsume      : 608
% 12.52/4.66  #Demod        : 6463
% 12.52/4.66  #Tautology    : 4433
% 12.52/4.66  #SimpNegUnit  : 52
% 12.52/4.66  #BackRed      : 116
% 12.52/4.66  
% 12.52/4.66  #Partial instantiations: 964
% 12.52/4.66  #Strategies tried      : 1
% 12.52/4.66  
% 12.52/4.66  Timing (in seconds)
% 12.52/4.66  ----------------------
% 12.52/4.67  Preprocessing        : 0.35
% 12.52/4.67  Parsing              : 0.18
% 12.52/4.67  CNF conversion       : 0.03
% 12.52/4.67  Main loop            : 3.51
% 12.52/4.67  Inferencing          : 0.93
% 12.52/4.67  Reduction            : 1.71
% 12.52/4.67  Demodulation         : 1.46
% 12.52/4.67  BG Simplification    : 0.09
% 12.52/4.67  Subsumption          : 0.59
% 12.52/4.67  Abstraction          : 0.12
% 12.52/4.67  MUC search           : 0.00
% 12.52/4.67  Cooper               : 0.00
% 12.52/4.67  Total                : 3.94
% 12.52/4.67  Index Insertion      : 0.00
% 12.52/4.67  Index Deletion       : 0.00
% 12.52/4.67  Index Matching       : 0.00
% 12.52/4.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
