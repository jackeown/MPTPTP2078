%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:31 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  111 (1616 expanded)
%              Number of leaves         :   44 ( 564 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 (1659 expanded)
%              Number of equality atoms :   76 (1514 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_90,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_89,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_327,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_350,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_327])).

tff(c_354,plain,(
    ! [A_95] : k4_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_350])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_364,plain,(
    ! [A_96] : r1_tarski(k1_xboole_0,A_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_20])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_368,plain,(
    ! [A_96] : k3_xboole_0(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_364,c_18])).

tff(c_120,plain,(
    ! [B_68,A_69] : k5_xboole_0(B_68,A_69) = k5_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_22])).

tff(c_790,plain,(
    ! [A_118,B_119] : k5_xboole_0(k5_xboole_0(A_118,B_119),k3_xboole_0(A_118,B_119)) = k2_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_845,plain,(
    ! [A_69] : k5_xboole_0(A_69,k3_xboole_0(k1_xboole_0,A_69)) = k2_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_790])).

tff(c_879,plain,(
    ! [A_69] : k2_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_368,c_845])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_552,plain,(
    ! [A_109,B_110,C_111] : k5_xboole_0(k5_xboole_0(A_109,B_110),C_111) = k5_xboole_0(A_109,k5_xboole_0(B_110,C_111)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2456,plain,(
    ! [B_208,A_209,C_210] : k5_xboole_0(k5_xboole_0(B_208,A_209),C_210) = k5_xboole_0(A_209,k5_xboole_0(B_208,C_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_552])).

tff(c_28,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2495,plain,(
    ! [A_209,B_208] : k5_xboole_0(A_209,k5_xboole_0(B_208,k3_xboole_0(B_208,A_209))) = k2_xboole_0(B_208,A_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2456,c_28])).

tff(c_3033,plain,(
    ! [A_221,B_222] : k5_xboole_0(A_221,k4_xboole_0(B_222,A_221)) = k2_xboole_0(B_222,A_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2495])).

tff(c_616,plain,(
    ! [A_24,C_111] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_552])).

tff(c_629,plain,(
    ! [A_24,C_111] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_111)) = C_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_616])).

tff(c_3139,plain,(
    ! [A_223,B_224] : k5_xboole_0(A_223,k2_xboole_0(B_224,A_223)) = k4_xboole_0(B_224,A_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_629])).

tff(c_3220,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k5_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3139])).

tff(c_3233,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3220])).

tff(c_644,plain,(
    ! [A_114,C_115] : k5_xboole_0(A_114,k5_xboole_0(A_114,C_115)) = C_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_616])).

tff(c_710,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k5_xboole_0(B_117,A_116)) = B_117 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_644])).

tff(c_743,plain,(
    ! [A_24,C_111] : k5_xboole_0(k5_xboole_0(A_24,C_111),C_111) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_710])).

tff(c_262,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1349,plain,(
    ! [A_158,B_159] : k3_xboole_0(k4_xboole_0(A_158,B_159),A_158) = k4_xboole_0(A_158,B_159) ),
    inference(resolution,[status(thm)],[c_20,c_262])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1765,plain,(
    ! [A_184,B_185] : k3_xboole_0(A_184,k4_xboole_0(A_184,B_185)) = k4_xboole_0(A_184,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_2])).

tff(c_1777,plain,(
    ! [A_184,B_185] : k5_xboole_0(k5_xboole_0(A_184,k4_xboole_0(A_184,B_185)),k4_xboole_0(A_184,B_185)) = k2_xboole_0(A_184,k4_xboole_0(A_184,B_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_28])).

tff(c_1812,plain,(
    ! [A_184,B_185] : k2_xboole_0(A_184,k4_xboole_0(A_184,B_185)) = A_184 ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_1777])).

tff(c_3255,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3233,c_1812])).

tff(c_3283,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3255])).

tff(c_3294,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_62])).

tff(c_3295,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_3294])).

tff(c_60,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3332,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3295,c_3295,c_60])).

tff(c_866,plain,(
    ! [A_7] : k5_xboole_0(k5_xboole_0(A_7,A_7),A_7) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_790])).

tff(c_880,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_26,c_866])).

tff(c_30,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_250,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_259,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = k2_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_250])).

tff(c_883,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_259])).

tff(c_3299,plain,(
    k3_tarski(k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3283,c_883])).

tff(c_3569,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3332,c_3295,c_3299])).

tff(c_3303,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3295,c_3283])).

tff(c_3578,plain,(
    k1_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_3303])).

tff(c_58,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_359,plain,(
    ! [A_95] : r1_tarski(k1_xboole_0,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_20])).

tff(c_46,plain,(
    ! [C_59,A_55] :
      ( r2_hidden(C_59,k1_zfmisc_1(A_55))
      | ~ r1_tarski(C_59,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_317,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_546,plain,(
    ! [A_107,C_108] :
      ( ~ r1_xboole_0(A_107,A_107)
      | ~ r2_hidden(C_108,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_317])).

tff(c_549,plain,(
    ! [C_108,B_6] :
      ( ~ r2_hidden(C_108,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_546])).

tff(c_631,plain,(
    ! [C_112,B_113] :
      ( ~ r2_hidden(C_112,B_113)
      | k1_xboole_0 != B_113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_549])).

tff(c_1233,plain,(
    ! [A_136,C_137] :
      ( k1_zfmisc_1(A_136) != k1_xboole_0
      | ~ r1_tarski(C_137,A_136) ) ),
    inference(resolution,[status(thm)],[c_46,c_631])).

tff(c_1250,plain,(
    ! [A_138] : k1_zfmisc_1(A_138) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_359,c_1233])).

tff(c_1252,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1250])).

tff(c_3313,plain,(
    k1_tarski('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3295,c_3295,c_1252])).

tff(c_3577,plain,(
    k1_tarski('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_3569,c_3313])).

tff(c_3603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3578,c_3577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.97  
% 4.70/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.70/1.97  
% 4.70/1.97  %Foreground sorts:
% 4.70/1.97  
% 4.70/1.97  
% 4.70/1.97  %Background operators:
% 4.70/1.97  
% 4.70/1.97  
% 4.70/1.97  %Foreground operators:
% 4.70/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.70/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.70/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.70/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.70/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.70/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.70/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.70/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.70/1.97  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.70/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.70/1.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.70/1.97  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.70/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.70/1.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.70/1.97  
% 4.85/1.99  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.85/1.99  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.85/1.99  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.85/1.99  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.85/1.99  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.85/1.99  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.85/1.99  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.85/1.99  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.85/1.99  tff(f_94, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.85/1.99  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.85/1.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.85/1.99  tff(f_90, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 4.85/1.99  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.85/1.99  tff(f_88, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.85/1.99  tff(f_89, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 4.85/1.99  tff(f_86, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.85/1.99  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.85/1.99  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.85/1.99  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.85/1.99  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.85/1.99  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.99  tff(c_327, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.85/1.99  tff(c_350, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_327])).
% 4.85/1.99  tff(c_354, plain, (![A_95]: (k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_350])).
% 4.85/1.99  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.85/1.99  tff(c_364, plain, (![A_96]: (r1_tarski(k1_xboole_0, A_96))), inference(superposition, [status(thm), theory('equality')], [c_354, c_20])).
% 4.85/1.99  tff(c_18, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/1.99  tff(c_368, plain, (![A_96]: (k3_xboole_0(k1_xboole_0, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_364, c_18])).
% 4.85/1.99  tff(c_120, plain, (![B_68, A_69]: (k5_xboole_0(B_68, A_69)=k5_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/1.99  tff(c_136, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_120, c_22])).
% 4.85/1.99  tff(c_790, plain, (![A_118, B_119]: (k5_xboole_0(k5_xboole_0(A_118, B_119), k3_xboole_0(A_118, B_119))=k2_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.85/1.99  tff(c_845, plain, (![A_69]: (k5_xboole_0(A_69, k3_xboole_0(k1_xboole_0, A_69))=k2_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_136, c_790])).
% 4.85/1.99  tff(c_879, plain, (![A_69]: (k2_xboole_0(k1_xboole_0, A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_368, c_845])).
% 4.85/1.99  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.85/1.99  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.85/1.99  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/1.99  tff(c_552, plain, (![A_109, B_110, C_111]: (k5_xboole_0(k5_xboole_0(A_109, B_110), C_111)=k5_xboole_0(A_109, k5_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.85/1.99  tff(c_2456, plain, (![B_208, A_209, C_210]: (k5_xboole_0(k5_xboole_0(B_208, A_209), C_210)=k5_xboole_0(A_209, k5_xboole_0(B_208, C_210)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_552])).
% 4.85/1.99  tff(c_28, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.85/1.99  tff(c_2495, plain, (![A_209, B_208]: (k5_xboole_0(A_209, k5_xboole_0(B_208, k3_xboole_0(B_208, A_209)))=k2_xboole_0(B_208, A_209))), inference(superposition, [status(thm), theory('equality')], [c_2456, c_28])).
% 4.85/1.99  tff(c_3033, plain, (![A_221, B_222]: (k5_xboole_0(A_221, k4_xboole_0(B_222, A_221))=k2_xboole_0(B_222, A_221))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2495])).
% 4.85/1.99  tff(c_616, plain, (![A_24, C_111]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_26, c_552])).
% 4.85/1.99  tff(c_629, plain, (![A_24, C_111]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_111))=C_111)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_616])).
% 4.85/1.99  tff(c_3139, plain, (![A_223, B_224]: (k5_xboole_0(A_223, k2_xboole_0(B_224, A_223))=k4_xboole_0(B_224, A_223))), inference(superposition, [status(thm), theory('equality')], [c_3033, c_629])).
% 4.85/1.99  tff(c_3220, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k5_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_3139])).
% 4.85/1.99  tff(c_3233, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3220])).
% 4.85/1.99  tff(c_644, plain, (![A_114, C_115]: (k5_xboole_0(A_114, k5_xboole_0(A_114, C_115))=C_115)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_616])).
% 4.85/1.99  tff(c_710, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k5_xboole_0(B_117, A_116))=B_117)), inference(superposition, [status(thm), theory('equality')], [c_4, c_644])).
% 4.85/1.99  tff(c_743, plain, (![A_24, C_111]: (k5_xboole_0(k5_xboole_0(A_24, C_111), C_111)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_629, c_710])).
% 4.85/1.99  tff(c_262, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/1.99  tff(c_1349, plain, (![A_158, B_159]: (k3_xboole_0(k4_xboole_0(A_158, B_159), A_158)=k4_xboole_0(A_158, B_159))), inference(resolution, [status(thm)], [c_20, c_262])).
% 4.85/1.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/1.99  tff(c_1765, plain, (![A_184, B_185]: (k3_xboole_0(A_184, k4_xboole_0(A_184, B_185))=k4_xboole_0(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_2])).
% 4.85/1.99  tff(c_1777, plain, (![A_184, B_185]: (k5_xboole_0(k5_xboole_0(A_184, k4_xboole_0(A_184, B_185)), k4_xboole_0(A_184, B_185))=k2_xboole_0(A_184, k4_xboole_0(A_184, B_185)))), inference(superposition, [status(thm), theory('equality')], [c_1765, c_28])).
% 4.85/1.99  tff(c_1812, plain, (![A_184, B_185]: (k2_xboole_0(A_184, k4_xboole_0(A_184, B_185))=A_184)), inference(demodulation, [status(thm), theory('equality')], [c_743, c_1777])).
% 4.85/1.99  tff(c_3255, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3233, c_1812])).
% 4.85/1.99  tff(c_3283, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3255])).
% 4.85/1.99  tff(c_3294, plain, (k2_xboole_0(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3283, c_62])).
% 4.85/1.99  tff(c_3295, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_879, c_3294])).
% 4.85/1.99  tff(c_60, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.85/1.99  tff(c_3332, plain, (k3_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3295, c_3295, c_60])).
% 4.85/1.99  tff(c_866, plain, (![A_7]: (k5_xboole_0(k5_xboole_0(A_7, A_7), A_7)=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_790])).
% 4.85/1.99  tff(c_880, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_26, c_866])).
% 4.85/1.99  tff(c_30, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/1.99  tff(c_250, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.85/1.99  tff(c_259, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=k2_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_250])).
% 4.85/1.99  tff(c_883, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_880, c_259])).
% 4.85/1.99  tff(c_3299, plain, (k3_tarski(k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3283, c_883])).
% 4.85/1.99  tff(c_3569, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3332, c_3295, c_3299])).
% 4.85/1.99  tff(c_3303, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3295, c_3283])).
% 4.85/1.99  tff(c_3578, plain, (k1_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_3303])).
% 4.85/1.99  tff(c_58, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.85/1.99  tff(c_359, plain, (![A_95]: (r1_tarski(k1_xboole_0, A_95))), inference(superposition, [status(thm), theory('equality')], [c_354, c_20])).
% 4.85/1.99  tff(c_46, plain, (![C_59, A_55]: (r2_hidden(C_59, k1_zfmisc_1(A_55)) | ~r1_tarski(C_59, A_55))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.85/1.99  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.85/1.99  tff(c_317, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, k3_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.85/1.99  tff(c_546, plain, (![A_107, C_108]: (~r1_xboole_0(A_107, A_107) | ~r2_hidden(C_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_10, c_317])).
% 4.85/1.99  tff(c_549, plain, (![C_108, B_6]: (~r2_hidden(C_108, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_546])).
% 4.85/1.99  tff(c_631, plain, (![C_112, B_113]: (~r2_hidden(C_112, B_113) | k1_xboole_0!=B_113)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_549])).
% 4.85/1.99  tff(c_1233, plain, (![A_136, C_137]: (k1_zfmisc_1(A_136)!=k1_xboole_0 | ~r1_tarski(C_137, A_136))), inference(resolution, [status(thm)], [c_46, c_631])).
% 4.85/1.99  tff(c_1250, plain, (![A_138]: (k1_zfmisc_1(A_138)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_359, c_1233])).
% 4.85/1.99  tff(c_1252, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_58, c_1250])).
% 4.85/1.99  tff(c_3313, plain, (k1_tarski('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3295, c_3295, c_1252])).
% 4.85/1.99  tff(c_3577, plain, (k1_tarski('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_3569, c_3313])).
% 4.85/1.99  tff(c_3603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3578, c_3577])).
% 4.85/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.99  
% 4.85/1.99  Inference rules
% 4.85/1.99  ----------------------
% 4.85/1.99  #Ref     : 0
% 4.85/1.99  #Sup     : 878
% 4.85/1.99  #Fact    : 0
% 4.85/1.99  #Define  : 0
% 4.85/1.99  #Split   : 1
% 4.85/1.99  #Chain   : 0
% 4.85/1.99  #Close   : 0
% 4.85/1.99  
% 4.85/1.99  Ordering : KBO
% 4.85/1.99  
% 4.85/1.99  Simplification rules
% 4.85/1.99  ----------------------
% 4.85/1.99  #Subsume      : 40
% 4.85/1.99  #Demod        : 638
% 4.85/1.99  #Tautology    : 532
% 4.85/1.99  #SimpNegUnit  : 6
% 4.85/1.99  #BackRed      : 44
% 4.85/1.99  
% 4.85/1.99  #Partial instantiations: 0
% 4.85/1.99  #Strategies tried      : 1
% 4.85/1.99  
% 4.85/1.99  Timing (in seconds)
% 4.85/1.99  ----------------------
% 4.85/2.00  Preprocessing        : 0.41
% 4.85/2.00  Parsing              : 0.21
% 4.85/2.00  CNF conversion       : 0.03
% 4.85/2.00  Main loop            : 0.77
% 4.85/2.00  Inferencing          : 0.24
% 4.85/2.00  Reduction            : 0.33
% 4.85/2.00  Demodulation         : 0.27
% 4.85/2.00  BG Simplification    : 0.04
% 4.85/2.00  Subsumption          : 0.12
% 4.85/2.00  Abstraction          : 0.04
% 4.85/2.00  MUC search           : 0.00
% 4.85/2.00  Cooper               : 0.00
% 4.85/2.00  Total                : 1.23
% 4.85/2.00  Index Insertion      : 0.00
% 4.85/2.00  Index Deletion       : 0.00
% 4.85/2.00  Index Matching       : 0.00
% 4.85/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
