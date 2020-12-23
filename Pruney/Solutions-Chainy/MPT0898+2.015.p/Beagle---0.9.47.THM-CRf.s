%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:51 EST 2020

% Result     : Theorem 36.73s
% Output     : CNFRefutation 36.73s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 805 expanded)
%              Number of leaves         :   42 ( 281 expanded)
%              Depth                    :   17
%              Number of atoms          :  250 (1423 expanded)
%              Number of equality atoms :  153 ( 908 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_zfmisc_1 > k3_zfmisc_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_139,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_34,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_236,plain,(
    ! [B_93,C_94,A_95] :
      ( r2_hidden(B_93,C_94)
      | ~ r1_tarski(k2_tarski(A_95,B_93),C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_248,plain,(
    ! [B_99,A_100] : r2_hidden(B_99,k2_tarski(A_100,B_99)) ),
    inference(resolution,[status(thm)],[c_106,c_236])).

tff(c_254,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_248])).

tff(c_26,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_zfmisc_1(k3_zfmisc_1(A_41,B_42,C_43),D_44) = k4_zfmisc_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_537,plain,(
    ! [C_137,D_138,A_139,B_140] :
      ( ~ r1_xboole_0(C_137,D_138)
      | r1_xboole_0(k2_zfmisc_1(A_139,C_137),k2_zfmisc_1(B_140,D_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [A_22] :
      ( ~ r1_xboole_0(A_22,A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_876,plain,(
    ! [B_170,D_171] :
      ( k2_zfmisc_1(B_170,D_171) = k1_xboole_0
      | ~ r1_xboole_0(D_171,D_171) ) ),
    inference(resolution,[status(thm)],[c_537,c_32])).

tff(c_893,plain,(
    ! [B_170,B_2] :
      ( k2_zfmisc_1(B_170,B_2) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_876])).

tff(c_987,plain,(
    ! [B_176,B_177] :
      ( k2_zfmisc_1(B_176,B_177) = k1_xboole_0
      | k1_xboole_0 != B_177 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_893])).

tff(c_1229,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( k4_zfmisc_1(A_190,B_191,C_192,D_193) = k1_xboole_0
      | k1_xboole_0 != D_193 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_987])).

tff(c_1259,plain,
    ( k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1229])).

tff(c_1350,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1259])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( ~ r1_xboole_0(A_28,B_29)
      | r1_xboole_0(k2_zfmisc_1(A_28,C_30),k2_zfmisc_1(B_29,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_298,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( ~ r1_xboole_0(A_112,B_113)
      | r1_xboole_0(k2_zfmisc_1(A_112,C_114),k2_zfmisc_1(B_113,D_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_321,plain,(
    ! [B_118,D_119] :
      ( k2_zfmisc_1(B_118,D_119) = k1_xboole_0
      | ~ r1_xboole_0(B_118,B_118) ) ),
    inference(resolution,[status(thm)],[c_298,c_32])).

tff(c_1984,plain,(
    ! [B_237,D_238,D_239] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_237,D_238),D_239) = k1_xboole_0
      | ~ r1_xboole_0(B_237,B_237) ) ),
    inference(resolution,[status(thm)],[c_42,c_321])).

tff(c_2001,plain,(
    ! [B_2,D_238,D_239] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_2,D_238),D_239) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1984])).

tff(c_2013,plain,(
    ! [D_238,D_239] : k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,D_238),D_239) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2001])).

tff(c_72,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_327,plain,(
    ! [B_2,D_119] :
      ( k2_zfmisc_1(B_2,D_119) = k1_xboole_0
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_321])).

tff(c_365,plain,(
    ! [D_119] : k2_zfmisc_1(k1_xboole_0,D_119) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_327])).

tff(c_332,plain,(
    ! [B_2,D_119] :
      ( k2_zfmisc_1(B_2,D_119) = k1_xboole_0
      | k1_xboole_0 != B_2 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_327])).

tff(c_1147,plain,(
    ! [A_186,B_187,C_188,D_189] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_186,B_187),C_188),D_189) = k4_zfmisc_1(A_186,B_187,C_188,D_189) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1215,plain,(
    ! [A_186,B_187,D_119,D_189] :
      ( k4_zfmisc_1(A_186,B_187,D_119,D_189) = k2_zfmisc_1(k1_xboole_0,D_189)
      | k2_zfmisc_1(A_186,B_187) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_1147])).

tff(c_2909,plain,(
    ! [A_276,B_277,D_278,D_279] :
      ( k4_zfmisc_1(A_276,B_277,D_278,D_279) = k1_xboole_0
      | k2_zfmisc_1(A_276,B_277) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_1215])).

tff(c_2947,plain,
    ( k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = k1_xboole_0
    | k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2909])).

tff(c_3049,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2947])).

tff(c_70,plain,(
    ! [A_52,B_53,C_54,D_55] : k3_zfmisc_1(k2_zfmisc_1(A_52,B_53),C_54,D_55) = k4_zfmisc_1(A_52,B_53,C_54,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_807,plain,(
    ! [A_163,B_164,C_165] :
      ( k3_zfmisc_1(A_163,B_164,C_165) != k1_xboole_0
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_164
      | k1_xboole_0 = A_163 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10947,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( k4_zfmisc_1(A_475,B_476,C_477,D_478) != k1_xboole_0
      | k1_xboole_0 = D_478
      | k1_xboole_0 = C_477
      | k2_zfmisc_1(A_475,B_476) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_807])).

tff(c_10992,plain,
    ( k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10947])).

tff(c_11007,plain,(
    k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3049,c_1350,c_1350,c_10992])).

tff(c_68,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_48,B_49),C_50),D_51) = k4_zfmisc_1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1272,plain,(
    ! [B_194,D_195,A_196,C_197] :
      ( r1_tarski(B_194,D_195)
      | k2_zfmisc_1(A_196,B_194) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_196,B_194),k2_zfmisc_1(C_197,D_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1275,plain,(
    ! [B_49,A_48,D_195,D_51,C_50,C_197] :
      ( r1_tarski(D_51,D_195)
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_48,B_49),C_50),D_51) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_48,B_49,C_50,D_51),k2_zfmisc_1(C_197,D_195)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1272])).

tff(c_27750,plain,(
    ! [B_835,A_836,C_837,D_839,C_838,D_834] :
      ( r1_tarski(D_834,D_839)
      | k4_zfmisc_1(A_836,B_835,C_837,D_834) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_836,B_835,C_837,D_834),k2_zfmisc_1(C_838,D_839)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1275])).

tff(c_182671,plain,(
    ! [D_2304,B_2303,C_2307,B_2301,A_2300,C_2306,A_2305,D_2302] :
      ( r1_tarski(D_2304,D_2302)
      | k4_zfmisc_1(A_2300,B_2301,C_2307,D_2304) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_2300,B_2301,C_2307,D_2304),k4_zfmisc_1(A_2305,B_2303,C_2306,D_2302)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_27750])).

tff(c_183108,plain,(
    ! [D_2308,A_2309,B_2310,C_2311] :
      ( r1_tarski(D_2308,'#skF_2')
      | k4_zfmisc_1(A_2309,B_2310,C_2311,D_2308) = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1(A_2309,B_2310,C_2311,D_2308),k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_182671])).

tff(c_183292,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_183108])).

tff(c_183401,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_11007,c_183292])).

tff(c_256,plain,(
    ! [A_101,B_102] :
      ( r2_xboole_0(A_101,B_102)
      | B_102 = A_101
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( ~ r2_xboole_0(B_21,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,(
    ! [B_102,A_101] :
      ( ~ r1_tarski(B_102,A_101)
      | B_102 = A_101
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_256,c_28])).

tff(c_183403,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_183401,c_267])).

tff(c_183406,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_183403])).

tff(c_182992,plain,(
    ! [D_2302,A_2305,B_2303,C_2306] :
      ( r1_tarski('#skF_2',D_2302)
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3'),k4_zfmisc_1(A_2305,B_2303,C_2306,D_2302)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_182671])).

tff(c_183103,plain,(
    ! [D_2302,A_2305,B_2303,C_2306] :
      ( r1_tarski('#skF_2',D_2302)
      | k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = k1_xboole_0
      | ~ r1_tarski(k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3'),k4_zfmisc_1(A_2305,B_2303,C_2306,D_2302)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_182992])).

tff(c_185177,plain,(
    ! [D_2331,A_2332,B_2333,C_2334] :
      ( r1_tarski('#skF_2',D_2331)
      | ~ r1_tarski(k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3'),k4_zfmisc_1(A_2332,B_2333,C_2334,D_2331)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11007,c_183103])).

tff(c_185361,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_185177])).

tff(c_185379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183406,c_185361])).

tff(c_185381,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2947])).

tff(c_185424,plain,(
    ! [C_50,D_51] : k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_50),D_51) = k4_zfmisc_1('#skF_2','#skF_2',C_50,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_185381,c_68])).

tff(c_185471,plain,(
    ! [C_50,D_51] : k4_zfmisc_1('#skF_2','#skF_2',C_50,D_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2013,c_185424])).

tff(c_714,plain,(
    ! [A_153,B_154,C_155,D_156] : k2_zfmisc_1(k3_zfmisc_1(A_153,B_154,C_155),D_156) = k4_zfmisc_1(A_153,B_154,C_155,D_156) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ! [A_32,B_33] :
      ( k2_zfmisc_1(A_32,k1_tarski(B_33)) != k1_xboole_0
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_186744,plain,(
    ! [A_2380,B_2381,C_2382,B_2383] :
      ( k4_zfmisc_1(A_2380,B_2381,C_2382,k1_tarski(B_2383)) != k1_xboole_0
      | k3_zfmisc_1(A_2380,B_2381,C_2382) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_44])).

tff(c_186802,plain,(
    ! [C_2384] : k3_zfmisc_1('#skF_2','#skF_2',C_2384) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_185471,c_186744])).

tff(c_60,plain,(
    ! [A_45,B_46,C_47] :
      ( k3_zfmisc_1(A_45,B_46,C_47) != k1_xboole_0
      | k1_xboole_0 = C_47
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_186807,plain,(
    ! [C_2384] :
      ( k1_xboole_0 = C_2384
      | k1_xboole_0 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186802,c_60])).

tff(c_186827,plain,(
    ! [C_2385] : k1_xboole_0 = C_2385 ),
    inference(negUnitSimplification,[status(thm)],[c_1350,c_1350,c_186807])).

tff(c_273,plain,(
    ! [A_103] : r2_hidden(A_103,k1_tarski(A_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_248])).

tff(c_223,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,k3_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_227,plain,(
    ! [A_91,C_92] :
      ( ~ r1_xboole_0(A_91,A_91)
      | ~ r2_hidden(C_92,A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_223])).

tff(c_230,plain,(
    ! [C_92,B_2] :
      ( ~ r2_hidden(C_92,B_2)
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_227])).

tff(c_234,plain,(
    ! [C_92,B_2] :
      ( ~ r2_hidden(C_92,B_2)
      | k1_xboole_0 != B_2 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_230])).

tff(c_277,plain,(
    ! [A_103] : k1_tarski(A_103) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_273,c_234])).

tff(c_901,plain,(
    ! [A_172,B_173,C_174] :
      ( r1_tarski(k2_tarski(A_172,B_173),C_174)
      | ~ r2_hidden(B_173,C_174)
      | ~ r2_hidden(A_172,C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1768,plain,(
    ! [A_226,C_227] :
      ( r1_tarski(k1_tarski(A_226),C_227)
      | ~ r2_hidden(A_226,C_227)
      | ~ r2_hidden(A_226,C_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_901])).

tff(c_443,plain,(
    ! [A_132,B_133] : k4_xboole_0(k2_xboole_0(A_132,B_133),k3_xboole_0(A_132,B_133)) = k5_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1043,plain,(
    ! [A_178] : k4_xboole_0(k2_xboole_0(A_178,A_178),A_178) = k5_xboole_0(A_178,A_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_443])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1053,plain,(
    ! [A_178] :
      ( k1_xboole_0 = A_178
      | ~ r1_tarski(A_178,k5_xboole_0(A_178,A_178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_24])).

tff(c_1772,plain,(
    ! [A_226] :
      ( k1_tarski(A_226) = k1_xboole_0
      | ~ r2_hidden(A_226,k5_xboole_0(k1_tarski(A_226),k1_tarski(A_226))) ) ),
    inference(resolution,[status(thm)],[c_1768,c_1053])).

tff(c_1788,plain,(
    ! [A_226] : ~ r2_hidden(A_226,k5_xboole_0(k1_tarski(A_226),k1_tarski(A_226))) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_1772])).

tff(c_186851,plain,(
    ! [A_226] : ~ r2_hidden(A_226,k5_xboole_0(k1_tarski(A_226),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186827,c_1788])).

tff(c_187013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_26,c_186851])).

tff(c_187015,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1259])).

tff(c_187050,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_2') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_26])).

tff(c_187043,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_4])).

tff(c_330,plain,(
    ! [B_29,D_31,D_119] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_29,D_31),D_119) = k1_xboole_0
      | ~ r1_xboole_0(B_29,B_29) ) ),
    inference(resolution,[status(thm)],[c_42,c_321])).

tff(c_188372,plain,(
    ! [B_4315,D_4316,D_4317] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_4315,D_4316),D_4317) = '#skF_2'
      | ~ r1_xboole_0(B_4315,B_4315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_330])).

tff(c_188375,plain,(
    ! [B_2,D_4316,D_4317] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_2,D_4316),D_4317) = '#skF_2'
      | k3_xboole_0(B_2,B_2) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_187043,c_188372])).

tff(c_188401,plain,(
    ! [D_4316,D_4317] : k2_zfmisc_1(k2_zfmisc_1('#skF_2',D_4316),D_4317) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188375])).

tff(c_66,plain,(
    ! [B_46,C_47] : k3_zfmisc_1(k1_xboole_0,B_46,C_47) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_617,plain,(
    ! [A_144,B_145,C_146,D_147] : k3_zfmisc_1(k2_zfmisc_1(A_144,B_145),C_146,D_147) = k4_zfmisc_1(A_144,B_145,C_146,D_147) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_634,plain,(
    ! [B_2,D_119,C_146,D_147] :
      ( k4_zfmisc_1(B_2,D_119,C_146,D_147) = k3_zfmisc_1(k1_xboole_0,C_146,D_147)
      | k1_xboole_0 != B_2 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_617])).

tff(c_1311,plain,(
    ! [B_198,D_199,C_200,D_201] :
      ( k4_zfmisc_1(B_198,D_199,C_200,D_201) = k1_xboole_0
      | k1_xboole_0 != B_198 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_634])).

tff(c_1341,plain,
    ( k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1311])).

tff(c_187056,plain,(
    k4_zfmisc_1('#skF_3','#skF_3','#skF_3','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_187015,c_1341])).

tff(c_810,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k4_zfmisc_1(A_52,B_53,C_54,D_55) != k1_xboole_0
      | k1_xboole_0 = D_55
      | k1_xboole_0 = C_54
      | k2_zfmisc_1(A_52,B_53) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_807])).

tff(c_189757,plain,(
    ! [A_4370,B_4371,C_4372,D_4373] :
      ( k4_zfmisc_1(A_4370,B_4371,C_4372,D_4373) != '#skF_2'
      | D_4373 = '#skF_2'
      | C_4372 = '#skF_2'
      | k2_zfmisc_1(A_4370,B_4371) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_187015,c_187015,c_187015,c_810])).

tff(c_189775,plain,
    ( '#skF_2' = '#skF_3'
    | k2_zfmisc_1('#skF_3','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_187056,c_189757])).

tff(c_189783,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_189775])).

tff(c_189829,plain,(
    ! [C_50,D_51] : k2_zfmisc_1(k2_zfmisc_1('#skF_2',C_50),D_51) = k4_zfmisc_1('#skF_3','#skF_3',C_50,D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_189783,c_68])).

tff(c_189877,plain,(
    ! [C_4374,D_4375] : k4_zfmisc_1('#skF_3','#skF_3',C_4374,D_4375) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188401,c_189829])).

tff(c_741,plain,(
    ! [A_153,B_154,C_155,B_33] :
      ( k4_zfmisc_1(A_153,B_154,C_155,k1_tarski(B_33)) != k1_xboole_0
      | k3_zfmisc_1(A_153,B_154,C_155) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_44])).

tff(c_188103,plain,(
    ! [A_153,B_154,C_155,B_33] :
      ( k4_zfmisc_1(A_153,B_154,C_155,k1_tarski(B_33)) != '#skF_2'
      | k3_zfmisc_1(A_153,B_154,C_155) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_187015,c_741])).

tff(c_189941,plain,(
    ! [C_4374] : k3_zfmisc_1('#skF_3','#skF_3',C_4374) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_189877,c_188103])).

tff(c_193730,plain,(
    ! [A_4479,B_4480,C_4481] :
      ( k3_zfmisc_1(A_4479,B_4480,C_4481) != '#skF_2'
      | C_4481 = '#skF_2'
      | B_4480 = '#skF_2'
      | A_4479 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_187015,c_187015,c_187015,c_60])).

tff(c_193745,plain,(
    ! [C_4374] :
      ( C_4374 = '#skF_2'
      | '#skF_2' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189941,c_193730])).

tff(c_193904,plain,(
    ! [C_4488] : C_4488 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_193745])).

tff(c_187037,plain,(
    ! [A_103] : k1_tarski(A_103) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_277])).

tff(c_920,plain,(
    ! [A_23,C_174] :
      ( r1_tarski(k1_tarski(A_23),C_174)
      | ~ r2_hidden(A_23,C_174)
      | ~ r2_hidden(A_23,C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_901])).

tff(c_187872,plain,(
    ! [A_4264] :
      ( A_4264 = '#skF_2'
      | ~ r1_tarski(A_4264,k5_xboole_0(A_4264,A_4264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187015,c_1053])).

tff(c_187880,plain,(
    ! [A_23] :
      ( k1_tarski(A_23) = '#skF_2'
      | ~ r2_hidden(A_23,k5_xboole_0(k1_tarski(A_23),k1_tarski(A_23))) ) ),
    inference(resolution,[status(thm)],[c_920,c_187872])).

tff(c_187898,plain,(
    ! [A_23] : ~ r2_hidden(A_23,k5_xboole_0(k1_tarski(A_23),k1_tarski(A_23))) ),
    inference(negUnitSimplification,[status(thm)],[c_187037,c_187880])).

tff(c_193945,plain,(
    ! [A_23] : ~ r2_hidden(A_23,k5_xboole_0(k1_tarski(A_23),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193904,c_187898])).

tff(c_194089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_187050,c_193945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:03:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.73/27.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.73/27.04  
% 36.73/27.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.73/27.04  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_zfmisc_1 > k3_zfmisc_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 36.73/27.04  
% 36.73/27.04  %Foreground sorts:
% 36.73/27.04  
% 36.73/27.04  
% 36.73/27.04  %Background operators:
% 36.73/27.04  
% 36.73/27.04  
% 36.73/27.04  %Foreground operators:
% 36.73/27.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.73/27.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.73/27.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.73/27.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.73/27.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.73/27.04  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 36.73/27.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 36.73/27.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.73/27.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.73/27.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.73/27.04  tff('#skF_2', type, '#skF_2': $i).
% 36.73/27.04  tff('#skF_3', type, '#skF_3': $i).
% 36.73/27.04  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 36.73/27.04  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 36.73/27.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.73/27.04  tff(k3_tarski, type, k3_tarski: $i > $i).
% 36.73/27.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.73/27.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.73/27.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.73/27.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.73/27.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.73/27.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.73/27.04  
% 36.73/27.07  tff(f_83, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 36.73/27.07  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 36.73/27.07  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 36.73/27.07  tff(f_116, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 36.73/27.07  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 36.73/27.07  tff(f_139, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 36.73/27.07  tff(f_118, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 36.73/27.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 36.73/27.07  tff(f_93, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 36.73/27.07  tff(f_81, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 36.73/27.07  tff(f_132, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 36.73/27.07  tff(f_134, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_zfmisc_1(A, B), C, D) = k4_zfmisc_1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_mcart_1)).
% 36.73/27.07  tff(f_130, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 36.73/27.07  tff(f_110, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 36.73/27.07  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 36.73/27.07  tff(f_69, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 36.73/27.07  tff(f_102, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 36.73/27.07  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 36.73/27.07  tff(f_54, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 36.73/27.07  tff(f_62, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 36.73/27.07  tff(c_34, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 36.73/27.07  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 36.73/27.07  tff(c_103, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.73/27.07  tff(c_106, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_103])).
% 36.73/27.07  tff(c_236, plain, (![B_93, C_94, A_95]: (r2_hidden(B_93, C_94) | ~r1_tarski(k2_tarski(A_95, B_93), C_94))), inference(cnfTransformation, [status(thm)], [f_116])).
% 36.73/27.07  tff(c_248, plain, (![B_99, A_100]: (r2_hidden(B_99, k2_tarski(A_100, B_99)))), inference(resolution, [status(thm)], [c_106, c_236])).
% 36.73/27.07  tff(c_254, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_248])).
% 36.73/27.07  tff(c_26, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_64])).
% 36.73/27.07  tff(c_74, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 36.73/27.07  tff(c_58, plain, (![A_41, B_42, C_43, D_44]: (k2_zfmisc_1(k3_zfmisc_1(A_41, B_42, C_43), D_44)=k4_zfmisc_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_118])).
% 36.73/27.07  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.73/27.07  tff(c_537, plain, (![C_137, D_138, A_139, B_140]: (~r1_xboole_0(C_137, D_138) | r1_xboole_0(k2_zfmisc_1(A_139, C_137), k2_zfmisc_1(B_140, D_138)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.73/27.07  tff(c_32, plain, (![A_22]: (~r1_xboole_0(A_22, A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 36.73/27.07  tff(c_876, plain, (![B_170, D_171]: (k2_zfmisc_1(B_170, D_171)=k1_xboole_0 | ~r1_xboole_0(D_171, D_171))), inference(resolution, [status(thm)], [c_537, c_32])).
% 36.73/27.07  tff(c_893, plain, (![B_170, B_2]: (k2_zfmisc_1(B_170, B_2)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_876])).
% 36.73/27.07  tff(c_987, plain, (![B_176, B_177]: (k2_zfmisc_1(B_176, B_177)=k1_xboole_0 | k1_xboole_0!=B_177)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_893])).
% 36.73/27.07  tff(c_1229, plain, (![A_190, B_191, C_192, D_193]: (k4_zfmisc_1(A_190, B_191, C_192, D_193)=k1_xboole_0 | k1_xboole_0!=D_193)), inference(superposition, [status(thm), theory('equality')], [c_58, c_987])).
% 36.73/27.07  tff(c_1259, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_74, c_1229])).
% 36.73/27.07  tff(c_1350, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_1259])).
% 36.73/27.07  tff(c_42, plain, (![A_28, B_29, C_30, D_31]: (~r1_xboole_0(A_28, B_29) | r1_xboole_0(k2_zfmisc_1(A_28, C_30), k2_zfmisc_1(B_29, D_31)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.73/27.07  tff(c_298, plain, (![A_112, B_113, C_114, D_115]: (~r1_xboole_0(A_112, B_113) | r1_xboole_0(k2_zfmisc_1(A_112, C_114), k2_zfmisc_1(B_113, D_115)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 36.73/27.07  tff(c_321, plain, (![B_118, D_119]: (k2_zfmisc_1(B_118, D_119)=k1_xboole_0 | ~r1_xboole_0(B_118, B_118))), inference(resolution, [status(thm)], [c_298, c_32])).
% 36.73/27.07  tff(c_1984, plain, (![B_237, D_238, D_239]: (k2_zfmisc_1(k2_zfmisc_1(B_237, D_238), D_239)=k1_xboole_0 | ~r1_xboole_0(B_237, B_237))), inference(resolution, [status(thm)], [c_42, c_321])).
% 36.73/27.07  tff(c_2001, plain, (![B_2, D_238, D_239]: (k2_zfmisc_1(k2_zfmisc_1(B_2, D_238), D_239)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1984])).
% 36.73/27.07  tff(c_2013, plain, (![D_238, D_239]: (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0, D_238), D_239)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2001])).
% 36.73/27.07  tff(c_72, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 36.73/27.07  tff(c_327, plain, (![B_2, D_119]: (k2_zfmisc_1(B_2, D_119)=k1_xboole_0 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_321])).
% 36.73/27.07  tff(c_365, plain, (![D_119]: (k2_zfmisc_1(k1_xboole_0, D_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_327])).
% 36.73/27.07  tff(c_332, plain, (![B_2, D_119]: (k2_zfmisc_1(B_2, D_119)=k1_xboole_0 | k1_xboole_0!=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_327])).
% 36.73/27.07  tff(c_1147, plain, (![A_186, B_187, C_188, D_189]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_186, B_187), C_188), D_189)=k4_zfmisc_1(A_186, B_187, C_188, D_189))), inference(cnfTransformation, [status(thm)], [f_132])).
% 36.73/27.07  tff(c_1215, plain, (![A_186, B_187, D_119, D_189]: (k4_zfmisc_1(A_186, B_187, D_119, D_189)=k2_zfmisc_1(k1_xboole_0, D_189) | k2_zfmisc_1(A_186, B_187)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_332, c_1147])).
% 36.73/27.07  tff(c_2909, plain, (![A_276, B_277, D_278, D_279]: (k4_zfmisc_1(A_276, B_277, D_278, D_279)=k1_xboole_0 | k2_zfmisc_1(A_276, B_277)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_365, c_1215])).
% 36.73/27.07  tff(c_2947, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_xboole_0 | k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_2909])).
% 36.73/27.07  tff(c_3049, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2947])).
% 36.73/27.07  tff(c_70, plain, (![A_52, B_53, C_54, D_55]: (k3_zfmisc_1(k2_zfmisc_1(A_52, B_53), C_54, D_55)=k4_zfmisc_1(A_52, B_53, C_54, D_55))), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.73/27.07  tff(c_807, plain, (![A_163, B_164, C_165]: (k3_zfmisc_1(A_163, B_164, C_165)!=k1_xboole_0 | k1_xboole_0=C_165 | k1_xboole_0=B_164 | k1_xboole_0=A_163)), inference(cnfTransformation, [status(thm)], [f_130])).
% 36.73/27.07  tff(c_10947, plain, (![A_475, B_476, C_477, D_478]: (k4_zfmisc_1(A_475, B_476, C_477, D_478)!=k1_xboole_0 | k1_xboole_0=D_478 | k1_xboole_0=C_477 | k2_zfmisc_1(A_475, B_476)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_807])).
% 36.73/27.07  tff(c_10992, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_10947])).
% 36.73/27.07  tff(c_11007, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3049, c_1350, c_1350, c_10992])).
% 36.73/27.07  tff(c_68, plain, (![A_48, B_49, C_50, D_51]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_48, B_49), C_50), D_51)=k4_zfmisc_1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_132])).
% 36.73/27.07  tff(c_1272, plain, (![B_194, D_195, A_196, C_197]: (r1_tarski(B_194, D_195) | k2_zfmisc_1(A_196, B_194)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_196, B_194), k2_zfmisc_1(C_197, D_195)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 36.73/27.07  tff(c_1275, plain, (![B_49, A_48, D_195, D_51, C_50, C_197]: (r1_tarski(D_51, D_195) | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_48, B_49), C_50), D_51)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_48, B_49, C_50, D_51), k2_zfmisc_1(C_197, D_195)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1272])).
% 36.73/27.07  tff(c_27750, plain, (![B_835, A_836, C_837, D_839, C_838, D_834]: (r1_tarski(D_834, D_839) | k4_zfmisc_1(A_836, B_835, C_837, D_834)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_836, B_835, C_837, D_834), k2_zfmisc_1(C_838, D_839)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1275])).
% 36.73/27.07  tff(c_182671, plain, (![D_2304, B_2303, C_2307, B_2301, A_2300, C_2306, A_2305, D_2302]: (r1_tarski(D_2304, D_2302) | k4_zfmisc_1(A_2300, B_2301, C_2307, D_2304)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_2300, B_2301, C_2307, D_2304), k4_zfmisc_1(A_2305, B_2303, C_2306, D_2302)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_27750])).
% 36.73/27.07  tff(c_183108, plain, (![D_2308, A_2309, B_2310, C_2311]: (r1_tarski(D_2308, '#skF_2') | k4_zfmisc_1(A_2309, B_2310, C_2311, D_2308)=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1(A_2309, B_2310, C_2311, D_2308), k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_182671])).
% 36.73/27.07  tff(c_183292, plain, (r1_tarski('#skF_3', '#skF_2') | k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_183108])).
% 36.73/27.07  tff(c_183401, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_11007, c_183292])).
% 36.73/27.07  tff(c_256, plain, (![A_101, B_102]: (r2_xboole_0(A_101, B_102) | B_102=A_101 | ~r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_36])).
% 36.73/27.07  tff(c_28, plain, (![B_21, A_20]: (~r2_xboole_0(B_21, A_20) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.73/27.07  tff(c_267, plain, (![B_102, A_101]: (~r1_tarski(B_102, A_101) | B_102=A_101 | ~r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_256, c_28])).
% 36.73/27.07  tff(c_183403, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_183401, c_267])).
% 36.73/27.07  tff(c_183406, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_183403])).
% 36.73/27.07  tff(c_182992, plain, (![D_2302, A_2305, B_2303, C_2306]: (r1_tarski('#skF_2', D_2302) | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3'), k4_zfmisc_1(A_2305, B_2303, C_2306, D_2302)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_182671])).
% 36.73/27.07  tff(c_183103, plain, (![D_2302, A_2305, B_2303, C_2306]: (r1_tarski('#skF_2', D_2302) | k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_xboole_0 | ~r1_tarski(k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3'), k4_zfmisc_1(A_2305, B_2303, C_2306, D_2302)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_182992])).
% 36.73/27.07  tff(c_185177, plain, (![D_2331, A_2332, B_2333, C_2334]: (r1_tarski('#skF_2', D_2331) | ~r1_tarski(k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3'), k4_zfmisc_1(A_2332, B_2333, C_2334, D_2331)))), inference(negUnitSimplification, [status(thm)], [c_11007, c_183103])).
% 36.73/27.07  tff(c_185361, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_106, c_185177])).
% 36.73/27.07  tff(c_185379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183406, c_185361])).
% 36.73/27.07  tff(c_185381, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2947])).
% 36.73/27.07  tff(c_185424, plain, (![C_50, D_51]: (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_50), D_51)=k4_zfmisc_1('#skF_2', '#skF_2', C_50, D_51))), inference(superposition, [status(thm), theory('equality')], [c_185381, c_68])).
% 36.73/27.07  tff(c_185471, plain, (![C_50, D_51]: (k4_zfmisc_1('#skF_2', '#skF_2', C_50, D_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2013, c_185424])).
% 36.73/27.07  tff(c_714, plain, (![A_153, B_154, C_155, D_156]: (k2_zfmisc_1(k3_zfmisc_1(A_153, B_154, C_155), D_156)=k4_zfmisc_1(A_153, B_154, C_155, D_156))), inference(cnfTransformation, [status(thm)], [f_118])).
% 36.73/27.07  tff(c_44, plain, (![A_32, B_33]: (k2_zfmisc_1(A_32, k1_tarski(B_33))!=k1_xboole_0 | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_102])).
% 36.73/27.07  tff(c_186744, plain, (![A_2380, B_2381, C_2382, B_2383]: (k4_zfmisc_1(A_2380, B_2381, C_2382, k1_tarski(B_2383))!=k1_xboole_0 | k3_zfmisc_1(A_2380, B_2381, C_2382)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_714, c_44])).
% 36.73/27.07  tff(c_186802, plain, (![C_2384]: (k3_zfmisc_1('#skF_2', '#skF_2', C_2384)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185471, c_186744])).
% 36.73/27.07  tff(c_60, plain, (![A_45, B_46, C_47]: (k3_zfmisc_1(A_45, B_46, C_47)!=k1_xboole_0 | k1_xboole_0=C_47 | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_130])).
% 36.73/27.07  tff(c_186807, plain, (![C_2384]: (k1_xboole_0=C_2384 | k1_xboole_0='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186802, c_60])).
% 36.73/27.07  tff(c_186827, plain, (![C_2385]: (k1_xboole_0=C_2385)), inference(negUnitSimplification, [status(thm)], [c_1350, c_1350, c_186807])).
% 36.73/27.07  tff(c_273, plain, (![A_103]: (r2_hidden(A_103, k1_tarski(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_248])).
% 36.73/27.07  tff(c_223, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, k3_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 36.73/27.07  tff(c_227, plain, (![A_91, C_92]: (~r1_xboole_0(A_91, A_91) | ~r2_hidden(C_92, A_91))), inference(superposition, [status(thm), theory('equality')], [c_12, c_223])).
% 36.73/27.07  tff(c_230, plain, (![C_92, B_2]: (~r2_hidden(C_92, B_2) | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_227])).
% 36.73/27.07  tff(c_234, plain, (![C_92, B_2]: (~r2_hidden(C_92, B_2) | k1_xboole_0!=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_230])).
% 36.73/27.07  tff(c_277, plain, (![A_103]: (k1_tarski(A_103)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_234])).
% 36.73/27.07  tff(c_901, plain, (![A_172, B_173, C_174]: (r1_tarski(k2_tarski(A_172, B_173), C_174) | ~r2_hidden(B_173, C_174) | ~r2_hidden(A_172, C_174))), inference(cnfTransformation, [status(thm)], [f_116])).
% 36.73/27.07  tff(c_1768, plain, (![A_226, C_227]: (r1_tarski(k1_tarski(A_226), C_227) | ~r2_hidden(A_226, C_227) | ~r2_hidden(A_226, C_227))), inference(superposition, [status(thm), theory('equality')], [c_34, c_901])).
% 36.73/27.07  tff(c_443, plain, (![A_132, B_133]: (k4_xboole_0(k2_xboole_0(A_132, B_133), k3_xboole_0(A_132, B_133))=k5_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_54])).
% 36.73/27.07  tff(c_1043, plain, (![A_178]: (k4_xboole_0(k2_xboole_0(A_178, A_178), A_178)=k5_xboole_0(A_178, A_178))), inference(superposition, [status(thm), theory('equality')], [c_12, c_443])).
% 36.73/27.07  tff(c_24, plain, (![A_17, B_18]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k4_xboole_0(B_18, A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 36.73/27.07  tff(c_1053, plain, (![A_178]: (k1_xboole_0=A_178 | ~r1_tarski(A_178, k5_xboole_0(A_178, A_178)))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_24])).
% 36.73/27.07  tff(c_1772, plain, (![A_226]: (k1_tarski(A_226)=k1_xboole_0 | ~r2_hidden(A_226, k5_xboole_0(k1_tarski(A_226), k1_tarski(A_226))))), inference(resolution, [status(thm)], [c_1768, c_1053])).
% 36.73/27.07  tff(c_1788, plain, (![A_226]: (~r2_hidden(A_226, k5_xboole_0(k1_tarski(A_226), k1_tarski(A_226))))), inference(negUnitSimplification, [status(thm)], [c_277, c_1772])).
% 36.73/27.07  tff(c_186851, plain, (![A_226]: (~r2_hidden(A_226, k5_xboole_0(k1_tarski(A_226), k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_186827, c_1788])).
% 36.73/27.07  tff(c_187013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_26, c_186851])).
% 36.73/27.07  tff(c_187015, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1259])).
% 36.73/27.07  tff(c_187050, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_2')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_26])).
% 36.73/27.07  tff(c_187043, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_4])).
% 36.73/27.07  tff(c_330, plain, (![B_29, D_31, D_119]: (k2_zfmisc_1(k2_zfmisc_1(B_29, D_31), D_119)=k1_xboole_0 | ~r1_xboole_0(B_29, B_29))), inference(resolution, [status(thm)], [c_42, c_321])).
% 36.73/27.07  tff(c_188372, plain, (![B_4315, D_4316, D_4317]: (k2_zfmisc_1(k2_zfmisc_1(B_4315, D_4316), D_4317)='#skF_2' | ~r1_xboole_0(B_4315, B_4315))), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_330])).
% 36.73/27.07  tff(c_188375, plain, (![B_2, D_4316, D_4317]: (k2_zfmisc_1(k2_zfmisc_1(B_2, D_4316), D_4317)='#skF_2' | k3_xboole_0(B_2, B_2)!='#skF_2')), inference(resolution, [status(thm)], [c_187043, c_188372])).
% 36.73/27.07  tff(c_188401, plain, (![D_4316, D_4317]: (k2_zfmisc_1(k2_zfmisc_1('#skF_2', D_4316), D_4317)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188375])).
% 36.73/27.07  tff(c_66, plain, (![B_46, C_47]: (k3_zfmisc_1(k1_xboole_0, B_46, C_47)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_130])).
% 36.73/27.07  tff(c_617, plain, (![A_144, B_145, C_146, D_147]: (k3_zfmisc_1(k2_zfmisc_1(A_144, B_145), C_146, D_147)=k4_zfmisc_1(A_144, B_145, C_146, D_147))), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.73/27.07  tff(c_634, plain, (![B_2, D_119, C_146, D_147]: (k4_zfmisc_1(B_2, D_119, C_146, D_147)=k3_zfmisc_1(k1_xboole_0, C_146, D_147) | k1_xboole_0!=B_2)), inference(superposition, [status(thm), theory('equality')], [c_332, c_617])).
% 36.73/27.07  tff(c_1311, plain, (![B_198, D_199, C_200, D_201]: (k4_zfmisc_1(B_198, D_199, C_200, D_201)=k1_xboole_0 | k1_xboole_0!=B_198)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_634])).
% 36.73/27.07  tff(c_1341, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_74, c_1311])).
% 36.73/27.07  tff(c_187056, plain, (k4_zfmisc_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_187015, c_1341])).
% 36.73/27.07  tff(c_810, plain, (![A_52, B_53, C_54, D_55]: (k4_zfmisc_1(A_52, B_53, C_54, D_55)!=k1_xboole_0 | k1_xboole_0=D_55 | k1_xboole_0=C_54 | k2_zfmisc_1(A_52, B_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_807])).
% 36.73/27.07  tff(c_189757, plain, (![A_4370, B_4371, C_4372, D_4373]: (k4_zfmisc_1(A_4370, B_4371, C_4372, D_4373)!='#skF_2' | D_4373='#skF_2' | C_4372='#skF_2' | k2_zfmisc_1(A_4370, B_4371)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_187015, c_187015, c_187015, c_810])).
% 36.73/27.07  tff(c_189775, plain, ('#skF_2'='#skF_3' | k2_zfmisc_1('#skF_3', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_187056, c_189757])).
% 36.73/27.07  tff(c_189783, plain, (k2_zfmisc_1('#skF_3', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_189775])).
% 36.73/27.07  tff(c_189829, plain, (![C_50, D_51]: (k2_zfmisc_1(k2_zfmisc_1('#skF_2', C_50), D_51)=k4_zfmisc_1('#skF_3', '#skF_3', C_50, D_51))), inference(superposition, [status(thm), theory('equality')], [c_189783, c_68])).
% 36.73/27.07  tff(c_189877, plain, (![C_4374, D_4375]: (k4_zfmisc_1('#skF_3', '#skF_3', C_4374, D_4375)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_188401, c_189829])).
% 36.73/27.07  tff(c_741, plain, (![A_153, B_154, C_155, B_33]: (k4_zfmisc_1(A_153, B_154, C_155, k1_tarski(B_33))!=k1_xboole_0 | k3_zfmisc_1(A_153, B_154, C_155)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_714, c_44])).
% 36.73/27.07  tff(c_188103, plain, (![A_153, B_154, C_155, B_33]: (k4_zfmisc_1(A_153, B_154, C_155, k1_tarski(B_33))!='#skF_2' | k3_zfmisc_1(A_153, B_154, C_155)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_187015, c_741])).
% 36.73/27.07  tff(c_189941, plain, (![C_4374]: (k3_zfmisc_1('#skF_3', '#skF_3', C_4374)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_189877, c_188103])).
% 36.73/27.07  tff(c_193730, plain, (![A_4479, B_4480, C_4481]: (k3_zfmisc_1(A_4479, B_4480, C_4481)!='#skF_2' | C_4481='#skF_2' | B_4480='#skF_2' | A_4479='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_187015, c_187015, c_187015, c_60])).
% 36.73/27.07  tff(c_193745, plain, (![C_4374]: (C_4374='#skF_2' | '#skF_2'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_189941, c_193730])).
% 36.73/27.07  tff(c_193904, plain, (![C_4488]: (C_4488='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_193745])).
% 36.73/27.07  tff(c_187037, plain, (![A_103]: (k1_tarski(A_103)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_277])).
% 36.73/27.07  tff(c_920, plain, (![A_23, C_174]: (r1_tarski(k1_tarski(A_23), C_174) | ~r2_hidden(A_23, C_174) | ~r2_hidden(A_23, C_174))), inference(superposition, [status(thm), theory('equality')], [c_34, c_901])).
% 36.73/27.07  tff(c_187872, plain, (![A_4264]: (A_4264='#skF_2' | ~r1_tarski(A_4264, k5_xboole_0(A_4264, A_4264)))), inference(demodulation, [status(thm), theory('equality')], [c_187015, c_1053])).
% 36.73/27.07  tff(c_187880, plain, (![A_23]: (k1_tarski(A_23)='#skF_2' | ~r2_hidden(A_23, k5_xboole_0(k1_tarski(A_23), k1_tarski(A_23))))), inference(resolution, [status(thm)], [c_920, c_187872])).
% 36.73/27.07  tff(c_187898, plain, (![A_23]: (~r2_hidden(A_23, k5_xboole_0(k1_tarski(A_23), k1_tarski(A_23))))), inference(negUnitSimplification, [status(thm)], [c_187037, c_187880])).
% 36.73/27.07  tff(c_193945, plain, (![A_23]: (~r2_hidden(A_23, k5_xboole_0(k1_tarski(A_23), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_193904, c_187898])).
% 36.73/27.07  tff(c_194089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_187050, c_193945])).
% 36.73/27.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.73/27.07  
% 36.73/27.07  Inference rules
% 36.73/27.07  ----------------------
% 36.73/27.07  #Ref     : 0
% 36.73/27.07  #Sup     : 48596
% 36.73/27.07  #Fact    : 0
% 36.73/27.07  #Define  : 0
% 36.73/27.07  #Split   : 15
% 36.73/27.07  #Chain   : 0
% 36.73/27.07  #Close   : 0
% 36.73/27.07  
% 36.73/27.07  Ordering : KBO
% 36.73/27.07  
% 36.73/27.07  Simplification rules
% 36.73/27.07  ----------------------
% 36.73/27.07  #Subsume      : 6446
% 36.73/27.07  #Demod        : 35053
% 36.73/27.07  #Tautology    : 36978
% 36.73/27.07  #SimpNegUnit  : 73
% 36.73/27.07  #BackRed      : 57
% 36.73/27.07  
% 36.73/27.07  #Partial instantiations: 180
% 36.73/27.07  #Strategies tried      : 1
% 36.73/27.07  
% 36.73/27.07  Timing (in seconds)
% 36.73/27.07  ----------------------
% 36.73/27.07  Preprocessing        : 0.35
% 36.73/27.07  Parsing              : 0.19
% 36.73/27.07  CNF conversion       : 0.02
% 36.73/27.07  Main loop            : 25.89
% 36.73/27.07  Inferencing          : 3.02
% 36.73/27.07  Reduction            : 14.04
% 36.73/27.07  Demodulation         : 12.04
% 36.73/27.07  BG Simplification    : 0.31
% 36.73/27.07  Subsumption          : 7.86
% 36.73/27.07  Abstraction          : 0.54
% 36.73/27.07  MUC search           : 0.00
% 36.73/27.07  Cooper               : 0.00
% 36.73/27.07  Total                : 26.29
% 36.73/27.07  Index Insertion      : 0.00
% 36.73/27.07  Index Deletion       : 0.00
% 36.73/27.07  Index Matching       : 0.00
% 36.73/27.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
