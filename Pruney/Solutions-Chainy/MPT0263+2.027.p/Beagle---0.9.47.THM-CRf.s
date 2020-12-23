%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 168 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 251 expanded)
%              Number of equality atoms :   44 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(k1_tarski(A_58),B_59)
      | r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_101,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_93,c_48])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_349,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(k1_tarski(A_90),B_91) = k1_xboole_0
      | r2_hidden(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_93,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_364,plain,(
    ! [A_90,B_91,C_14] :
      ( ~ r1_xboole_0(k1_tarski(A_90),B_91)
      | ~ r2_hidden(C_14,k1_xboole_0)
      | r2_hidden(A_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_16])).

tff(c_4267,plain,(
    ! [C_280] : ~ r2_hidden(C_280,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_4278,plain,(
    ! [A_281] : r1_xboole_0(A_281,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_4267])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4299,plain,(
    ! [A_281] : k4_xboole_0(A_281,k1_xboole_0) = A_281 ),
    inference(resolution,[status(thm)],[c_4278,c_22])).

tff(c_5097,plain,(
    ! [A_289] : k4_xboole_0(A_289,k1_xboole_0) = A_289 ),
    inference(resolution,[status(thm)],[c_4278,c_22])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_181,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_184,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,k4_xboole_0(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_20])).

tff(c_2089,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_184])).

tff(c_211,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,k3_xboole_0(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_20])).

tff(c_240,plain,(
    ! [A_81,B_82] : k3_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_217])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_393,plain,(
    ! [A_95,B_96] : k3_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_217])).

tff(c_2485,plain,(
    ! [A_211,B_212,C_213] :
      ( ~ r1_xboole_0(A_211,k3_xboole_0(A_211,B_212))
      | ~ r2_hidden(C_213,k3_xboole_0(A_211,B_212)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_16])).

tff(c_2527,plain,(
    ! [C_213,A_3,B_212] :
      ( ~ r2_hidden(C_213,k3_xboole_0(A_3,B_212))
      | k3_xboole_0(A_3,k3_xboole_0(A_3,B_212)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2485])).

tff(c_2605,plain,(
    ! [C_217,A_218,B_219] :
      ( ~ r2_hidden(C_217,k3_xboole_0(A_218,B_219))
      | k3_xboole_0(A_218,B_219) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_2527])).

tff(c_2608,plain,(
    ! [C_217,A_79,B_80] :
      ( ~ r2_hidden(C_217,k4_xboole_0(A_79,B_80))
      | k3_xboole_0(A_79,k4_xboole_0(A_79,B_80)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2089,c_2605])).

tff(c_2653,plain,(
    ! [C_217,A_79,B_80] :
      ( ~ r2_hidden(C_217,k4_xboole_0(A_79,B_80))
      | k4_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2089,c_2608])).

tff(c_5131,plain,(
    ! [C_217,A_289] :
      ( ~ r2_hidden(C_217,A_289)
      | k4_xboole_0(A_289,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5097,c_2653])).

tff(c_6052,plain,(
    ! [C_301,A_302] :
      ( ~ r2_hidden(C_301,A_302)
      | k1_xboole_0 != A_302 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4299,c_5131])).

tff(c_6191,plain,(
    ! [A_306,B_307] :
      ( k1_xboole_0 != A_306
      | r1_xboole_0(A_306,B_307) ) ),
    inference(resolution,[status(thm)],[c_12,c_6052])).

tff(c_238,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_164,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_242,plain,(
    ! [A_83,B_84,A_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | r1_xboole_0(A_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_1246,plain,(
    ! [A_165,A_166,B_167] :
      ( k4_xboole_0(A_165,k3_xboole_0(A_166,B_167)) = A_165
      | ~ r1_xboole_0(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_242,c_22])).

tff(c_1319,plain,(
    ! [B_2,A_1] :
      ( k4_xboole_0(B_2,A_1) = B_2
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_1246])).

tff(c_7667,plain,(
    ! [B_307] : k4_xboole_0(B_307,k1_xboole_0) = B_307 ),
    inference(resolution,[status(thm)],[c_6191,c_1319])).

tff(c_44,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(k1_tarski(A_51),B_52) = k1_xboole_0
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3873,plain,(
    ! [A_276,B_277] :
      ( k4_xboole_0(k1_tarski(A_276),k1_xboole_0) = k3_xboole_0(k1_tarski(A_276),B_277)
      | ~ r2_hidden(A_276,B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_4073,plain,(
    ! [A_276,B_277] :
      ( k4_xboole_0(k1_tarski(A_276),k1_xboole_0) = k3_xboole_0(B_277,k1_tarski(A_276))
      | ~ r2_hidden(A_276,B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3873,c_2])).

tff(c_16060,plain,(
    ! [B_456,A_457] :
      ( k3_xboole_0(B_456,k1_tarski(A_457)) = k1_tarski(A_457)
      | ~ r2_hidden(A_457,B_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7667,c_4073])).

tff(c_46,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_49,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_16301,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16060,c_49])).

tff(c_16389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_16301])).

tff(c_16391,plain,(
    ! [A_458,B_459] :
      ( ~ r1_xboole_0(k1_tarski(A_458),B_459)
      | r2_hidden(A_458,B_459) ) ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_16460,plain,(
    ! [A_49,B_50] : r2_hidden(A_49,B_50) ),
    inference(resolution,[status(thm)],[c_40,c_16391])).

tff(c_178,plain,(
    ! [B_2,A_1,C_78] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_78,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_164])).

tff(c_16505,plain,(
    ! [B_2,A_1] : ~ r1_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16460,c_178])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16567,plain,(
    ! [A_467,B_468] : k4_xboole_0(A_467,B_468) != A_467 ),
    inference(negUnitSimplification,[status(thm)],[c_16505,c_24])).

tff(c_16577,plain,(
    ! [A_469,B_470] : k3_xboole_0(A_469,B_470) != A_469 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_16567])).

tff(c_16589,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) != A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_16577])).

tff(c_16602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16589,c_2089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/2.90  
% 8.31/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/2.90  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.31/2.90  
% 8.31/2.90  %Foreground sorts:
% 8.31/2.90  
% 8.31/2.90  
% 8.31/2.90  %Background operators:
% 8.31/2.90  
% 8.31/2.90  
% 8.31/2.90  %Foreground operators:
% 8.31/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/2.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.31/2.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.31/2.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.31/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.31/2.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.31/2.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.31/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.31/2.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.31/2.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.31/2.90  tff('#skF_3', type, '#skF_3': $i).
% 8.31/2.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.31/2.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/2.90  tff('#skF_4', type, '#skF_4': $i).
% 8.31/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/2.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.31/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.31/2.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/2.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.31/2.90  
% 8.55/2.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.55/2.92  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.55/2.92  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.55/2.92  tff(f_99, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 8.55/2.92  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.55/2.92  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.55/2.92  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.55/2.92  tff(f_71, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.55/2.92  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.55/2.92  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 8.55/2.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.55/2.92  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.92  tff(c_40, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.55/2.92  tff(c_93, plain, (![A_58, B_59]: (r1_xboole_0(k1_tarski(A_58), B_59) | r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.55/2.92  tff(c_48, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.55/2.92  tff(c_101, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_93, c_48])).
% 8.55/2.92  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.55/2.92  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.55/2.92  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.92  tff(c_349, plain, (![A_90, B_91]: (k3_xboole_0(k1_tarski(A_90), B_91)=k1_xboole_0 | r2_hidden(A_90, B_91))), inference(resolution, [status(thm)], [c_93, c_4])).
% 8.55/2.92  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.92  tff(c_364, plain, (![A_90, B_91, C_14]: (~r1_xboole_0(k1_tarski(A_90), B_91) | ~r2_hidden(C_14, k1_xboole_0) | r2_hidden(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_349, c_16])).
% 8.55/2.92  tff(c_4267, plain, (![C_280]: (~r2_hidden(C_280, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_364])).
% 8.55/2.92  tff(c_4278, plain, (![A_281]: (r1_xboole_0(A_281, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_4267])).
% 8.55/2.92  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.55/2.92  tff(c_4299, plain, (![A_281]: (k4_xboole_0(A_281, k1_xboole_0)=A_281)), inference(resolution, [status(thm)], [c_4278, c_22])).
% 8.55/2.92  tff(c_5097, plain, (![A_289]: (k4_xboole_0(A_289, k1_xboole_0)=A_289)), inference(resolution, [status(thm)], [c_4278, c_22])).
% 8.55/2.92  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.55/2.92  tff(c_181, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.55/2.92  tff(c_184, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k3_xboole_0(A_79, k4_xboole_0(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_20])).
% 8.55/2.92  tff(c_2089, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_184])).
% 8.55/2.92  tff(c_211, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.55/2.92  tff(c_217, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, k3_xboole_0(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_211, c_20])).
% 8.55/2.92  tff(c_240, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_217])).
% 8.55/2.92  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.55/2.92  tff(c_393, plain, (![A_95, B_96]: (k3_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_217])).
% 8.55/2.92  tff(c_2485, plain, (![A_211, B_212, C_213]: (~r1_xboole_0(A_211, k3_xboole_0(A_211, B_212)) | ~r2_hidden(C_213, k3_xboole_0(A_211, B_212)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_16])).
% 8.55/2.92  tff(c_2527, plain, (![C_213, A_3, B_212]: (~r2_hidden(C_213, k3_xboole_0(A_3, B_212)) | k3_xboole_0(A_3, k3_xboole_0(A_3, B_212))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2485])).
% 8.55/2.92  tff(c_2605, plain, (![C_217, A_218, B_219]: (~r2_hidden(C_217, k3_xboole_0(A_218, B_219)) | k3_xboole_0(A_218, B_219)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_2527])).
% 8.55/2.92  tff(c_2608, plain, (![C_217, A_79, B_80]: (~r2_hidden(C_217, k4_xboole_0(A_79, B_80)) | k3_xboole_0(A_79, k4_xboole_0(A_79, B_80))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2089, c_2605])).
% 8.55/2.92  tff(c_2653, plain, (![C_217, A_79, B_80]: (~r2_hidden(C_217, k4_xboole_0(A_79, B_80)) | k4_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2089, c_2608])).
% 8.55/2.92  tff(c_5131, plain, (![C_217, A_289]: (~r2_hidden(C_217, A_289) | k4_xboole_0(A_289, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5097, c_2653])).
% 8.55/2.92  tff(c_6052, plain, (![C_301, A_302]: (~r2_hidden(C_301, A_302) | k1_xboole_0!=A_302)), inference(demodulation, [status(thm), theory('equality')], [c_4299, c_5131])).
% 8.55/2.92  tff(c_6191, plain, (![A_306, B_307]: (k1_xboole_0!=A_306 | r1_xboole_0(A_306, B_307))), inference(resolution, [status(thm)], [c_12, c_6052])).
% 8.55/2.92  tff(c_238, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 8.55/2.92  tff(c_164, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.55/2.92  tff(c_242, plain, (![A_83, B_84, A_85]: (~r1_xboole_0(A_83, B_84) | r1_xboole_0(A_85, k3_xboole_0(A_83, B_84)))), inference(resolution, [status(thm)], [c_10, c_164])).
% 8.55/2.92  tff(c_1246, plain, (![A_165, A_166, B_167]: (k4_xboole_0(A_165, k3_xboole_0(A_166, B_167))=A_165 | ~r1_xboole_0(A_166, B_167))), inference(resolution, [status(thm)], [c_242, c_22])).
% 8.55/2.92  tff(c_1319, plain, (![B_2, A_1]: (k4_xboole_0(B_2, A_1)=B_2 | ~r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_238, c_1246])).
% 8.55/2.92  tff(c_7667, plain, (![B_307]: (k4_xboole_0(B_307, k1_xboole_0)=B_307)), inference(resolution, [status(thm)], [c_6191, c_1319])).
% 8.55/2.92  tff(c_44, plain, (![A_51, B_52]: (k4_xboole_0(k1_tarski(A_51), B_52)=k1_xboole_0 | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.55/2.92  tff(c_3873, plain, (![A_276, B_277]: (k4_xboole_0(k1_tarski(A_276), k1_xboole_0)=k3_xboole_0(k1_tarski(A_276), B_277) | ~r2_hidden(A_276, B_277))), inference(superposition, [status(thm), theory('equality')], [c_44, c_181])).
% 8.55/2.92  tff(c_4073, plain, (![A_276, B_277]: (k4_xboole_0(k1_tarski(A_276), k1_xboole_0)=k3_xboole_0(B_277, k1_tarski(A_276)) | ~r2_hidden(A_276, B_277))), inference(superposition, [status(thm), theory('equality')], [c_3873, c_2])).
% 8.55/2.92  tff(c_16060, plain, (![B_456, A_457]: (k3_xboole_0(B_456, k1_tarski(A_457))=k1_tarski(A_457) | ~r2_hidden(A_457, B_456))), inference(demodulation, [status(thm), theory('equality')], [c_7667, c_4073])).
% 8.55/2.92  tff(c_46, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.55/2.92  tff(c_49, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 8.55/2.92  tff(c_16301, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16060, c_49])).
% 8.55/2.92  tff(c_16389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_16301])).
% 8.55/2.92  tff(c_16391, plain, (![A_458, B_459]: (~r1_xboole_0(k1_tarski(A_458), B_459) | r2_hidden(A_458, B_459))), inference(splitRight, [status(thm)], [c_364])).
% 8.55/2.92  tff(c_16460, plain, (![A_49, B_50]: (r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_40, c_16391])).
% 8.55/2.92  tff(c_178, plain, (![B_2, A_1, C_78]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_78, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_164])).
% 8.55/2.92  tff(c_16505, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_16460, c_178])).
% 8.55/2.92  tff(c_24, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.55/2.92  tff(c_16567, plain, (![A_467, B_468]: (k4_xboole_0(A_467, B_468)!=A_467)), inference(negUnitSimplification, [status(thm)], [c_16505, c_24])).
% 8.55/2.92  tff(c_16577, plain, (![A_469, B_470]: (k3_xboole_0(A_469, B_470)!=A_469)), inference(superposition, [status(thm), theory('equality')], [c_20, c_16567])).
% 8.55/2.92  tff(c_16589, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)!=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_16577])).
% 8.55/2.92  tff(c_16602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16589, c_2089])).
% 8.55/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/2.92  
% 8.55/2.92  Inference rules
% 8.55/2.92  ----------------------
% 8.55/2.92  #Ref     : 6
% 8.55/2.92  #Sup     : 4248
% 8.55/2.92  #Fact    : 2
% 8.55/2.92  #Define  : 0
% 8.55/2.92  #Split   : 2
% 8.55/2.92  #Chain   : 0
% 8.55/2.92  #Close   : 0
% 8.55/2.92  
% 8.55/2.92  Ordering : KBO
% 8.55/2.92  
% 8.55/2.92  Simplification rules
% 8.55/2.92  ----------------------
% 8.55/2.92  #Subsume      : 1957
% 8.55/2.92  #Demod        : 1374
% 8.55/2.92  #Tautology    : 1101
% 8.55/2.92  #SimpNegUnit  : 108
% 8.55/2.92  #BackRed      : 43
% 8.55/2.92  
% 8.55/2.92  #Partial instantiations: 0
% 8.55/2.92  #Strategies tried      : 1
% 8.55/2.92  
% 8.55/2.92  Timing (in seconds)
% 8.55/2.92  ----------------------
% 8.55/2.92  Preprocessing        : 0.31
% 8.55/2.92  Parsing              : 0.17
% 8.55/2.92  CNF conversion       : 0.02
% 8.55/2.92  Main loop            : 1.85
% 8.55/2.92  Inferencing          : 0.48
% 8.55/2.92  Reduction            : 0.71
% 8.55/2.92  Demodulation         : 0.56
% 8.55/2.92  BG Simplification    : 0.06
% 8.55/2.92  Subsumption          : 0.46
% 8.55/2.92  Abstraction          : 0.08
% 8.55/2.92  MUC search           : 0.00
% 8.55/2.92  Cooper               : 0.00
% 8.55/2.92  Total                : 2.19
% 8.55/2.92  Index Insertion      : 0.00
% 8.55/2.92  Index Deletion       : 0.00
% 8.55/2.92  Index Matching       : 0.00
% 8.55/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
