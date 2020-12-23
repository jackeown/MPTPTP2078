%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 288 expanded)
%              Number of leaves         :   36 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  119 ( 439 expanded)
%              Number of equality atoms :   53 ( 238 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_339,plain,(
    ! [B_78,A_79] :
      ( k3_xboole_0(B_78,k1_tarski(A_79)) = k1_tarski(A_79)
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_125,plain,(
    ! [A_59,B_60] : k3_xboole_0(A_59,k2_xboole_0(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_351,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_134])).

tff(c_375,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_38,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(k1_tarski(A_45),B_46)
      | r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_298,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_319,plain,(
    ! [A_76,B_77] :
      ( ~ r1_xboole_0(A_76,B_77)
      | v1_xboole_0(k3_xboole_0(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_8,c_298])).

tff(c_394,plain,(
    ! [B_84,A_85] :
      ( ~ r1_xboole_0(B_84,A_85)
      | v1_xboole_0(k3_xboole_0(A_85,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_406,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_394])).

tff(c_426,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_429,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_426])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_429])).

tff(c_434,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_10,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_438,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_434,c_10])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_438])).

tff(c_443,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_476,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_626,plain,(
    ! [A_98,B_99] : k5_xboole_0(k5_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k2_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5930,plain,(
    ! [B_242,A_243] : k5_xboole_0(k5_xboole_0(B_242,A_243),k3_xboole_0(A_243,B_242)) = k2_xboole_0(A_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_626])).

tff(c_677,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_626])).

tff(c_6139,plain,(
    ! [B_244,A_245] : k2_xboole_0(B_244,A_245) = k2_xboole_0(A_245,B_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_5930,c_677])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6725,plain,(
    ! [B_250,A_251] : k3_xboole_0(B_250,k2_xboole_0(A_251,B_250)) = B_250 ),
    inference(superposition,[status(thm),theory(equality)],[c_6139,c_16])).

tff(c_6838,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_6725])).

tff(c_48,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_318,plain,(
    ! [A_73,B_74] :
      ( ~ r1_xboole_0(A_73,B_74)
      | v1_xboole_0(k3_xboole_0(A_73,B_74)) ) ),
    inference(resolution,[status(thm)],[c_8,c_298])).

tff(c_535,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_2'(A_92,B_93),k3_xboole_0(A_92,B_93))
      | r1_xboole_0(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_598,plain,(
    ! [A_96,B_97] :
      ( ~ v1_xboole_0(k3_xboole_0(A_96,B_97))
      | r1_xboole_0(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_535,c_6])).

tff(c_701,plain,(
    ! [A_100,B_101] :
      ( ~ v1_xboole_0(k3_xboole_0(A_100,B_101))
      | r1_xboole_0(B_101,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_598])).

tff(c_738,plain,(
    ! [B_103,A_104] :
      ( r1_xboole_0(B_103,A_104)
      | ~ r1_xboole_0(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_318,c_701])).

tff(c_1592,plain,(
    ! [B_156,A_157] :
      ( r1_xboole_0(B_156,k1_tarski(A_157))
      | r2_hidden(A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_38,c_738])).

tff(c_1611,plain,(
    ! [B_156] :
      ( r1_xboole_0(B_156,'#skF_4')
      | r2_hidden('#skF_3',B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_1592])).

tff(c_146,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_162,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_18])).

tff(c_22,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_808,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k5_xboole_0(A_110,B_111),C_112) = k5_xboole_0(A_110,k5_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_867,plain,(
    ! [A_21,C_112] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_112)) = k5_xboole_0(k1_xboole_0,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_808])).

tff(c_885,plain,(
    ! [A_21,C_112] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_112)) = C_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_867])).

tff(c_2429,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(k1_tarski(A_184),B_185) = k1_tarski(A_184)
      | ~ r2_hidden(A_184,B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_339])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2468,plain,(
    ! [A_184,B_185] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_184),B_185),k1_tarski(A_184)) = k2_xboole_0(k1_tarski(A_184),B_185)
      | ~ r2_hidden(A_184,B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_24])).

tff(c_2970,plain,(
    ! [A_200,B_201] :
      ( k2_xboole_0(k1_tarski(A_200),B_201) = B_201
      | ~ r2_hidden(A_200,B_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_4,c_2468])).

tff(c_3037,plain,(
    ! [B_202] :
      ( k2_xboole_0('#skF_4',B_202) = B_202
      | ~ r2_hidden('#skF_3',B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_2970])).

tff(c_3047,plain,(
    ! [B_156] :
      ( k2_xboole_0('#skF_4',B_156) = B_156
      | r1_xboole_0(B_156,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1611,c_3037])).

tff(c_6914,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6838,c_318])).

tff(c_6996,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6914])).

tff(c_7002,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3047,c_6996])).

tff(c_7014,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_7002])).

tff(c_7016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7014])).

tff(c_7017,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6914])).

tff(c_582,plain,(
    ! [B_94] :
      ( r1_xboole_0('#skF_4',B_94)
      | r2_hidden('#skF_3',B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_38])).

tff(c_591,plain,(
    ! [B_94] :
      ( ~ v1_xboole_0(B_94)
      | r1_xboole_0('#skF_4',B_94) ) ),
    inference(resolution,[status(thm)],[c_582,c_6])).

tff(c_743,plain,(
    ! [B_94] :
      ( r1_xboole_0(B_94,'#skF_4')
      | ~ v1_xboole_0(B_94) ) ),
    inference(resolution,[status(thm)],[c_591,c_738])).

tff(c_1270,plain,(
    ! [A_125,B_126] :
      ( k3_xboole_0(A_125,B_126) = k1_xboole_0
      | ~ r1_xboole_0(A_125,B_126) ) ),
    inference(resolution,[status(thm)],[c_319,c_10])).

tff(c_1285,plain,(
    ! [B_94] :
      ( k3_xboole_0(B_94,'#skF_4') = k1_xboole_0
      | ~ v1_xboole_0(B_94) ) ),
    inference(resolution,[status(thm)],[c_743,c_1270])).

tff(c_7021,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7017,c_1285])).

tff(c_7029,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6838,c_7021])).

tff(c_7031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_7029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.24  
% 5.93/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.24  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.93/2.24  
% 5.93/2.24  %Foreground sorts:
% 5.93/2.24  
% 5.93/2.24  
% 5.93/2.24  %Background operators:
% 5.93/2.24  
% 5.93/2.24  
% 5.93/2.24  %Foreground operators:
% 5.93/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.93/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.93/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.93/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.93/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.93/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.93/2.24  tff('#skF_5', type, '#skF_5': $i).
% 5.93/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.93/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.93/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.93/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.93/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.93/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.93/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.93/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.93/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.93/2.24  
% 5.93/2.26  tff(f_99, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 5.93/2.26  tff(f_84, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.93/2.26  tff(f_55, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.93/2.26  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.93/2.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.93/2.26  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.93/2.26  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.93/2.26  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.93/2.26  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.93/2.26  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.93/2.26  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.93/2.26  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.93/2.26  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.93/2.26  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.93/2.26  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.93/2.26  tff(c_339, plain, (![B_78, A_79]: (k3_xboole_0(B_78, k1_tarski(A_79))=k1_tarski(A_79) | ~r2_hidden(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.93/2.26  tff(c_50, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.93/2.26  tff(c_125, plain, (![A_59, B_60]: (k3_xboole_0(A_59, k2_xboole_0(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.93/2.26  tff(c_134, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_50, c_125])).
% 5.93/2.26  tff(c_351, plain, (k1_tarski('#skF_3')='#skF_4' | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_339, c_134])).
% 5.93/2.26  tff(c_375, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_351])).
% 5.93/2.26  tff(c_38, plain, (![A_45, B_46]: (r1_xboole_0(k1_tarski(A_45), B_46) | r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.93/2.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.93/2.26  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.93/2.26  tff(c_298, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.93/2.26  tff(c_319, plain, (![A_76, B_77]: (~r1_xboole_0(A_76, B_77) | v1_xboole_0(k3_xboole_0(A_76, B_77)))), inference(resolution, [status(thm)], [c_8, c_298])).
% 5.93/2.26  tff(c_394, plain, (![B_84, A_85]: (~r1_xboole_0(B_84, A_85) | v1_xboole_0(k3_xboole_0(A_85, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 5.93/2.26  tff(c_406, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_134, c_394])).
% 5.93/2.26  tff(c_426, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_406])).
% 5.93/2.26  tff(c_429, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_426])).
% 5.93/2.26  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_429])).
% 5.93/2.26  tff(c_434, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_406])).
% 5.93/2.26  tff(c_10, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.93/2.26  tff(c_438, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_434, c_10])).
% 5.93/2.26  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_438])).
% 5.93/2.26  tff(c_443, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_351])).
% 5.93/2.26  tff(c_476, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_50])).
% 5.93/2.26  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.93/2.26  tff(c_626, plain, (![A_98, B_99]: (k5_xboole_0(k5_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k2_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.93/2.26  tff(c_5930, plain, (![B_242, A_243]: (k5_xboole_0(k5_xboole_0(B_242, A_243), k3_xboole_0(A_243, B_242))=k2_xboole_0(A_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_4, c_626])).
% 5.93/2.26  tff(c_677, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_626])).
% 5.93/2.26  tff(c_6139, plain, (![B_244, A_245]: (k2_xboole_0(B_244, A_245)=k2_xboole_0(A_245, B_244))), inference(superposition, [status(thm), theory('equality')], [c_5930, c_677])).
% 5.93/2.26  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k2_xboole_0(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.93/2.26  tff(c_6725, plain, (![B_250, A_251]: (k3_xboole_0(B_250, k2_xboole_0(A_251, B_250))=B_250)), inference(superposition, [status(thm), theory('equality')], [c_6139, c_16])).
% 5.93/2.26  tff(c_6838, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_476, c_6725])).
% 5.93/2.26  tff(c_48, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.93/2.26  tff(c_318, plain, (![A_73, B_74]: (~r1_xboole_0(A_73, B_74) | v1_xboole_0(k3_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_8, c_298])).
% 5.93/2.26  tff(c_535, plain, (![A_92, B_93]: (r2_hidden('#skF_2'(A_92, B_93), k3_xboole_0(A_92, B_93)) | r1_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.93/2.26  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.93/2.26  tff(c_598, plain, (![A_96, B_97]: (~v1_xboole_0(k3_xboole_0(A_96, B_97)) | r1_xboole_0(A_96, B_97))), inference(resolution, [status(thm)], [c_535, c_6])).
% 5.93/2.26  tff(c_701, plain, (![A_100, B_101]: (~v1_xboole_0(k3_xboole_0(A_100, B_101)) | r1_xboole_0(B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_2, c_598])).
% 5.93/2.26  tff(c_738, plain, (![B_103, A_104]: (r1_xboole_0(B_103, A_104) | ~r1_xboole_0(A_104, B_103))), inference(resolution, [status(thm)], [c_318, c_701])).
% 5.93/2.26  tff(c_1592, plain, (![B_156, A_157]: (r1_xboole_0(B_156, k1_tarski(A_157)) | r2_hidden(A_157, B_156))), inference(resolution, [status(thm)], [c_38, c_738])).
% 5.93/2.26  tff(c_1611, plain, (![B_156]: (r1_xboole_0(B_156, '#skF_4') | r2_hidden('#skF_3', B_156))), inference(superposition, [status(thm), theory('equality')], [c_443, c_1592])).
% 5.93/2.26  tff(c_146, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.93/2.26  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.93/2.26  tff(c_162, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_146, c_18])).
% 5.93/2.26  tff(c_22, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.93/2.26  tff(c_808, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k5_xboole_0(A_110, B_111), C_112)=k5_xboole_0(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.93/2.26  tff(c_867, plain, (![A_21, C_112]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_112))=k5_xboole_0(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_22, c_808])).
% 5.93/2.26  tff(c_885, plain, (![A_21, C_112]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_112))=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_867])).
% 5.93/2.26  tff(c_2429, plain, (![A_184, B_185]: (k3_xboole_0(k1_tarski(A_184), B_185)=k1_tarski(A_184) | ~r2_hidden(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_2, c_339])).
% 5.93/2.26  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.93/2.26  tff(c_2468, plain, (![A_184, B_185]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_184), B_185), k1_tarski(A_184))=k2_xboole_0(k1_tarski(A_184), B_185) | ~r2_hidden(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_2429, c_24])).
% 5.93/2.26  tff(c_2970, plain, (![A_200, B_201]: (k2_xboole_0(k1_tarski(A_200), B_201)=B_201 | ~r2_hidden(A_200, B_201))), inference(demodulation, [status(thm), theory('equality')], [c_885, c_4, c_2468])).
% 5.93/2.26  tff(c_3037, plain, (![B_202]: (k2_xboole_0('#skF_4', B_202)=B_202 | ~r2_hidden('#skF_3', B_202))), inference(superposition, [status(thm), theory('equality')], [c_443, c_2970])).
% 5.93/2.26  tff(c_3047, plain, (![B_156]: (k2_xboole_0('#skF_4', B_156)=B_156 | r1_xboole_0(B_156, '#skF_4'))), inference(resolution, [status(thm)], [c_1611, c_3037])).
% 5.93/2.26  tff(c_6914, plain, (~r1_xboole_0('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6838, c_318])).
% 5.93/2.26  tff(c_6996, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_6914])).
% 5.93/2.26  tff(c_7002, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3047, c_6996])).
% 5.93/2.26  tff(c_7014, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_476, c_7002])).
% 5.93/2.26  tff(c_7016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_7014])).
% 5.93/2.26  tff(c_7017, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_6914])).
% 5.93/2.26  tff(c_582, plain, (![B_94]: (r1_xboole_0('#skF_4', B_94) | r2_hidden('#skF_3', B_94))), inference(superposition, [status(thm), theory('equality')], [c_443, c_38])).
% 5.93/2.26  tff(c_591, plain, (![B_94]: (~v1_xboole_0(B_94) | r1_xboole_0('#skF_4', B_94))), inference(resolution, [status(thm)], [c_582, c_6])).
% 5.93/2.26  tff(c_743, plain, (![B_94]: (r1_xboole_0(B_94, '#skF_4') | ~v1_xboole_0(B_94))), inference(resolution, [status(thm)], [c_591, c_738])).
% 5.93/2.26  tff(c_1270, plain, (![A_125, B_126]: (k3_xboole_0(A_125, B_126)=k1_xboole_0 | ~r1_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_319, c_10])).
% 5.93/2.26  tff(c_1285, plain, (![B_94]: (k3_xboole_0(B_94, '#skF_4')=k1_xboole_0 | ~v1_xboole_0(B_94))), inference(resolution, [status(thm)], [c_743, c_1270])).
% 5.93/2.26  tff(c_7021, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_7017, c_1285])).
% 5.93/2.26  tff(c_7029, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6838, c_7021])).
% 5.93/2.26  tff(c_7031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_7029])).
% 5.93/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.26  
% 5.93/2.26  Inference rules
% 5.93/2.26  ----------------------
% 5.93/2.26  #Ref     : 0
% 5.93/2.26  #Sup     : 1723
% 5.93/2.26  #Fact    : 0
% 5.93/2.26  #Define  : 0
% 5.93/2.26  #Split   : 11
% 5.93/2.26  #Chain   : 0
% 5.93/2.26  #Close   : 0
% 5.93/2.26  
% 5.93/2.26  Ordering : KBO
% 5.93/2.26  
% 5.93/2.26  Simplification rules
% 5.93/2.26  ----------------------
% 5.93/2.26  #Subsume      : 429
% 5.93/2.26  #Demod        : 781
% 5.93/2.26  #Tautology    : 622
% 5.93/2.26  #SimpNegUnit  : 189
% 5.93/2.26  #BackRed      : 20
% 5.93/2.26  
% 5.93/2.26  #Partial instantiations: 0
% 5.93/2.26  #Strategies tried      : 1
% 5.93/2.26  
% 5.93/2.26  Timing (in seconds)
% 5.93/2.26  ----------------------
% 5.93/2.26  Preprocessing        : 0.35
% 5.93/2.26  Parsing              : 0.19
% 5.93/2.26  CNF conversion       : 0.02
% 5.93/2.26  Main loop            : 1.09
% 5.93/2.26  Inferencing          : 0.35
% 5.93/2.26  Reduction            : 0.45
% 5.93/2.26  Demodulation         : 0.35
% 5.93/2.26  BG Simplification    : 0.04
% 5.93/2.26  Subsumption          : 0.17
% 5.93/2.26  Abstraction          : 0.05
% 5.93/2.26  MUC search           : 0.00
% 5.93/2.26  Cooper               : 0.00
% 5.93/2.26  Total                : 1.48
% 5.93/2.26  Index Insertion      : 0.00
% 5.93/2.26  Index Deletion       : 0.00
% 5.93/2.26  Index Matching       : 0.00
% 5.93/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
