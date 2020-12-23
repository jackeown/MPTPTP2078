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
% DateTime   : Thu Dec  3 09:47:30 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 245 expanded)
%              Number of leaves         :   39 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :   79 ( 267 expanded)
%              Number of equality atoms :   65 ( 233 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_68,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1534,plain,(
    ! [A_157,B_158,C_159,D_160] : k2_xboole_0(k1_enumset1(A_157,B_158,C_159),k1_tarski(D_160)) = k2_enumset1(A_157,B_158,C_159,D_160) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1570,plain,(
    ! [A_38,B_39,D_160] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_160)) = k2_enumset1(A_38,A_38,B_39,D_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1534])).

tff(c_2312,plain,(
    ! [A_195,B_196,D_197] : k2_xboole_0(k2_tarski(A_195,B_196),k1_tarski(D_197)) = k1_enumset1(A_195,B_196,D_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1570])).

tff(c_2339,plain,(
    ! [A_37,D_197] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_197)) = k1_enumset1(A_37,A_37,D_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2312])).

tff(c_2342,plain,(
    ! [A_37,D_197] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_197)) = k2_tarski(A_37,D_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2339])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_232])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_774,plain,(
    ! [A_133,B_134,C_135] : k5_xboole_0(k5_xboole_0(A_133,B_134),C_135) = k5_xboole_0(A_133,k5_xboole_0(B_134,C_135)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2853,plain,(
    ! [A_220,C_221] : k5_xboole_0(k4_xboole_0(A_220,A_220),C_221) = k5_xboole_0(A_220,k5_xboole_0(A_220,C_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_774])).

tff(c_2899,plain,(
    ! [A_220] : k5_xboole_0(A_220,k5_xboole_0(A_220,k4_xboole_0(A_220,A_220))) = k4_xboole_0(k4_xboole_0(A_220,A_220),k4_xboole_0(A_220,A_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_256])).

tff(c_3356,plain,(
    ! [A_233] : k4_xboole_0(k4_xboole_0(A_233,A_233),k4_xboole_0(A_233,A_233)) = k4_xboole_0(A_233,A_233) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_24,c_2899])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_88,B_89] : k3_xboole_0(k4_xboole_0(A_88,B_89),B_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_175,plain,(
    ! [B_89,A_88] : k3_xboole_0(B_89,k4_xboole_0(A_88,B_89)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2])).

tff(c_3495,plain,(
    ! [A_235] : k3_xboole_0(k4_xboole_0(A_235,A_235),k4_xboole_0(A_235,A_235)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3356,c_175])).

tff(c_3506,plain,(
    ! [A_235] : k4_xboole_0(A_235,A_235) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3495,c_10])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_216,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_216])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_301,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_12])).

tff(c_962,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_256])).

tff(c_3564,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3506,c_962])).

tff(c_3668,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3564,c_24])).

tff(c_3688,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_18,c_3668])).

tff(c_1573,plain,(
    ! [A_38,B_39,D_160] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_160)) = k1_enumset1(A_38,B_39,D_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1570])).

tff(c_4186,plain,(
    ! [D_160] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_160)) = k1_enumset1('#skF_4','#skF_3',D_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_3688,c_1573])).

tff(c_4802,plain,(
    ! [D_284] : k1_enumset1('#skF_4','#skF_3',D_284) = k2_tarski('#skF_4',D_284) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_4186])).

tff(c_30,plain,(
    ! [E_29,A_23,C_25] : r2_hidden(E_29,k1_enumset1(A_23,E_29,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4931,plain,(
    ! [D_289] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_289)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4802,c_30])).

tff(c_1207,plain,(
    ! [E_148,C_149,B_150,A_151] :
      ( E_148 = C_149
      | E_148 = B_150
      | E_148 = A_151
      | ~ r2_hidden(E_148,k1_enumset1(A_151,B_150,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1219,plain,(
    ! [E_148,B_39,A_38] :
      ( E_148 = B_39
      | E_148 = A_38
      | E_148 = A_38
      | ~ r2_hidden(E_148,k2_tarski(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1207])).

tff(c_4934,plain,(
    ! [D_289] :
      ( D_289 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_4931,c_1219])).

tff(c_4947,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_4934])).

tff(c_4943,plain,(
    ! [D_289] : D_289 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_4934])).

tff(c_5287,plain,(
    ! [D_4674] : D_4674 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4947,c_4943])).

tff(c_5605,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.61/2.07  
% 5.61/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.61/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.61/2.07  
% 5.61/2.07  %Foreground sorts:
% 5.61/2.07  
% 5.61/2.07  
% 5.61/2.07  %Background operators:
% 5.61/2.07  
% 5.61/2.07  
% 5.61/2.07  %Foreground operators:
% 5.61/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.61/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.61/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.61/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.61/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.61/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.61/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.61/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.61/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.61/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.61/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.61/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.61/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.61/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.61/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.61/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.61/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.61/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.61/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.61/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.61/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.61/2.07  
% 5.61/2.09  tff(f_89, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.61/2.09  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.61/2.09  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.61/2.09  tff(f_76, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.61/2.09  tff(f_70, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 5.61/2.09  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.61/2.09  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.61/2.09  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.61/2.09  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.61/2.09  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.61/2.09  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.61/2.09  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.61/2.09  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.61/2.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.61/2.09  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.61/2.09  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.61/2.09  tff(c_68, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.61/2.09  tff(c_56, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.61/2.09  tff(c_54, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.61/2.09  tff(c_58, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.61/2.09  tff(c_1534, plain, (![A_157, B_158, C_159, D_160]: (k2_xboole_0(k1_enumset1(A_157, B_158, C_159), k1_tarski(D_160))=k2_enumset1(A_157, B_158, C_159, D_160))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.61/2.09  tff(c_1570, plain, (![A_38, B_39, D_160]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_160))=k2_enumset1(A_38, A_38, B_39, D_160))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1534])).
% 5.61/2.09  tff(c_2312, plain, (![A_195, B_196, D_197]: (k2_xboole_0(k2_tarski(A_195, B_196), k1_tarski(D_197))=k1_enumset1(A_195, B_196, D_197))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1570])).
% 5.61/2.09  tff(c_2339, plain, (![A_37, D_197]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_197))=k1_enumset1(A_37, A_37, D_197))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2312])).
% 5.61/2.09  tff(c_2342, plain, (![A_37, D_197]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_197))=k2_tarski(A_37, D_197))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2339])).
% 5.61/2.09  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.61/2.09  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.61/2.09  tff(c_232, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.61/2.09  tff(c_256, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_232])).
% 5.61/2.09  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.61/2.09  tff(c_24, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.61/2.09  tff(c_774, plain, (![A_133, B_134, C_135]: (k5_xboole_0(k5_xboole_0(A_133, B_134), C_135)=k5_xboole_0(A_133, k5_xboole_0(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.61/2.09  tff(c_2853, plain, (![A_220, C_221]: (k5_xboole_0(k4_xboole_0(A_220, A_220), C_221)=k5_xboole_0(A_220, k5_xboole_0(A_220, C_221)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_774])).
% 5.61/2.09  tff(c_2899, plain, (![A_220]: (k5_xboole_0(A_220, k5_xboole_0(A_220, k4_xboole_0(A_220, A_220)))=k4_xboole_0(k4_xboole_0(A_220, A_220), k4_xboole_0(A_220, A_220)))), inference(superposition, [status(thm), theory('equality')], [c_2853, c_256])).
% 5.61/2.09  tff(c_3356, plain, (![A_233]: (k4_xboole_0(k4_xboole_0(A_233, A_233), k4_xboole_0(A_233, A_233))=k4_xboole_0(A_233, A_233))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_24, c_2899])).
% 5.61/2.09  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.61/2.09  tff(c_158, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.61/2.09  tff(c_167, plain, (![A_88, B_89]: (k3_xboole_0(k4_xboole_0(A_88, B_89), B_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_158])).
% 5.61/2.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.61/2.09  tff(c_175, plain, (![B_89, A_88]: (k3_xboole_0(B_89, k4_xboole_0(A_88, B_89))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_167, c_2])).
% 5.61/2.09  tff(c_3495, plain, (![A_235]: (k3_xboole_0(k4_xboole_0(A_235, A_235), k4_xboole_0(A_235, A_235))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3356, c_175])).
% 5.61/2.09  tff(c_3506, plain, (![A_235]: (k4_xboole_0(A_235, A_235)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3495, c_10])).
% 5.61/2.09  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.61/2.09  tff(c_216, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.61/2.09  tff(c_220, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_70, c_216])).
% 5.61/2.09  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.61/2.09  tff(c_301, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_12])).
% 5.61/2.09  tff(c_962, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_256])).
% 5.61/2.09  tff(c_3564, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3506, c_962])).
% 5.61/2.09  tff(c_3668, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3564, c_24])).
% 5.61/2.09  tff(c_3688, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_18, c_3668])).
% 5.61/2.09  tff(c_1573, plain, (![A_38, B_39, D_160]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_160))=k1_enumset1(A_38, B_39, D_160))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1570])).
% 5.61/2.09  tff(c_4186, plain, (![D_160]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_160))=k1_enumset1('#skF_4', '#skF_3', D_160))), inference(superposition, [status(thm), theory('equality')], [c_3688, c_1573])).
% 5.61/2.09  tff(c_4802, plain, (![D_284]: (k1_enumset1('#skF_4', '#skF_3', D_284)=k2_tarski('#skF_4', D_284))), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_4186])).
% 5.61/2.09  tff(c_30, plain, (![E_29, A_23, C_25]: (r2_hidden(E_29, k1_enumset1(A_23, E_29, C_25)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.61/2.09  tff(c_4931, plain, (![D_289]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_289)))), inference(superposition, [status(thm), theory('equality')], [c_4802, c_30])).
% 5.61/2.09  tff(c_1207, plain, (![E_148, C_149, B_150, A_151]: (E_148=C_149 | E_148=B_150 | E_148=A_151 | ~r2_hidden(E_148, k1_enumset1(A_151, B_150, C_149)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.61/2.09  tff(c_1219, plain, (![E_148, B_39, A_38]: (E_148=B_39 | E_148=A_38 | E_148=A_38 | ~r2_hidden(E_148, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1207])).
% 5.61/2.09  tff(c_4934, plain, (![D_289]: (D_289='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_4931, c_1219])).
% 5.61/2.09  tff(c_4947, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_4934])).
% 5.61/2.09  tff(c_4943, plain, (![D_289]: (D_289='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_4934])).
% 5.61/2.09  tff(c_5287, plain, (![D_4674]: (D_4674='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4947, c_4943])).
% 5.61/2.09  tff(c_5605, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5287, c_68])).
% 5.61/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.61/2.09  
% 5.61/2.09  Inference rules
% 5.61/2.09  ----------------------
% 5.61/2.09  #Ref     : 0
% 5.61/2.09  #Sup     : 1468
% 5.61/2.09  #Fact    : 0
% 5.61/2.09  #Define  : 0
% 5.61/2.09  #Split   : 0
% 5.61/2.09  #Chain   : 0
% 5.61/2.09  #Close   : 0
% 5.61/2.09  
% 5.61/2.09  Ordering : KBO
% 5.61/2.09  
% 5.61/2.09  Simplification rules
% 5.61/2.09  ----------------------
% 5.61/2.09  #Subsume      : 117
% 5.61/2.09  #Demod        : 1040
% 5.61/2.09  #Tautology    : 825
% 5.61/2.09  #SimpNegUnit  : 1
% 5.61/2.09  #BackRed      : 39
% 5.61/2.09  
% 5.61/2.09  #Partial instantiations: 84
% 5.61/2.09  #Strategies tried      : 1
% 5.61/2.09  
% 5.61/2.09  Timing (in seconds)
% 5.61/2.09  ----------------------
% 5.61/2.09  Preprocessing        : 0.33
% 5.61/2.09  Parsing              : 0.17
% 5.61/2.09  CNF conversion       : 0.02
% 5.61/2.09  Main loop            : 1.00
% 5.61/2.09  Inferencing          : 0.36
% 5.61/2.09  Reduction            : 0.40
% 5.61/2.09  Demodulation         : 0.32
% 5.61/2.09  BG Simplification    : 0.04
% 5.61/2.09  Subsumption          : 0.15
% 5.61/2.09  Abstraction          : 0.05
% 5.61/2.09  MUC search           : 0.00
% 5.61/2.09  Cooper               : 0.00
% 5.61/2.09  Total                : 1.37
% 5.61/2.09  Index Insertion      : 0.00
% 5.61/2.09  Index Deletion       : 0.00
% 5.61/2.09  Index Matching       : 0.00
% 5.61/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
