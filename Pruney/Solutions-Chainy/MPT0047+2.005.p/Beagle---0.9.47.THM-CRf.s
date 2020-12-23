%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:47 EST 2020

% Result     : Theorem 45.13s
% Output     : CNFRefutation 45.26s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 348 expanded)
%              Number of leaves         :   30 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  134 ( 417 expanded)
%              Number of equality atoms :   78 ( 285 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_61,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_145,plain,(
    ! [A_50,B_49] : r1_tarski(A_50,k2_xboole_0(B_49,A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_52])).

tff(c_38,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_388,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_412,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_388])).

tff(c_593,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_627,plain,(
    ! [A_36,B_37] : k2_xboole_0(k2_xboole_0(A_36,B_37),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_593])).

tff(c_1046,plain,(
    ! [A_107,B_108] : k2_xboole_0(k2_xboole_0(A_107,B_108),A_107) = k2_xboole_0(A_107,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_627])).

tff(c_1111,plain,(
    ! [B_2,B_108] : k2_xboole_0(B_2,k2_xboole_0(B_2,B_108)) = k2_xboole_0(B_2,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1046])).

tff(c_50,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_407,plain,(
    ! [A_50,B_49] : k4_xboole_0(A_50,k2_xboole_0(B_49,A_50)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_388])).

tff(c_624,plain,(
    ! [B_49,A_50] : k2_xboole_0(k2_xboole_0(B_49,A_50),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_593])).

tff(c_3632,plain,(
    ! [B_188,A_189] : k2_xboole_0(k2_xboole_0(B_188,A_189),A_189) = k2_xboole_0(B_188,A_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_624])).

tff(c_4025,plain,(
    ! [A_195,B_196] : k2_xboole_0(A_195,k2_xboole_0(B_196,A_195)) = k2_xboole_0(B_196,A_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3632])).

tff(c_29008,plain,(
    ! [B_474,A_475] : k2_xboole_0(B_474,k2_xboole_0(B_474,A_475)) = k2_xboole_0(A_475,B_474) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4025])).

tff(c_29360,plain,(
    ! [B_35,A_34] : k2_xboole_0(k4_xboole_0(B_35,A_34),A_34) = k2_xboole_0(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_29008])).

tff(c_29447,plain,(
    ! [B_35,A_34] : k2_xboole_0(k4_xboole_0(B_35,A_34),A_34) = k2_xboole_0(A_34,B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_29360])).

tff(c_64,plain,(
    ! [A_39,B_40] : r1_tarski(A_39,k2_xboole_0(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_67,plain,(
    ! [A_20] : r1_tarski(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_411,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_67,c_388])).

tff(c_636,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_593])).

tff(c_651,plain,(
    ! [A_20] : k2_xboole_0(A_20,A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_636])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_32,B_33] : r1_tarski(k4_xboole_0(A_32,B_33),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_410,plain,(
    ! [A_32,B_33] : k4_xboole_0(k4_xboole_0(A_32,B_33),A_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_388])).

tff(c_630,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k2_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_593])).

tff(c_761,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_630])).

tff(c_40,plain,(
    ! [A_21,B_22] : k3_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_142,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,k2_xboole_0(A_50,B_49)) = B_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_40])).

tff(c_2794,plain,(
    ! [A_162,B_163] : k3_xboole_0(k4_xboole_0(A_162,B_163),A_162) = k4_xboole_0(A_162,B_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_142])).

tff(c_2869,plain,(
    ! [B_4,B_163] : k3_xboole_0(B_4,k4_xboole_0(B_4,B_163)) = k4_xboole_0(B_4,B_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2794])).

tff(c_152,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_38])).

tff(c_612,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_152])).

tff(c_643,plain,(
    ! [B_85] : k4_xboole_0(B_85,k1_xboole_0) = B_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_612])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_183,plain,(
    ! [A_51] : k2_xboole_0(k1_xboole_0,A_51) = A_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_38])).

tff(c_198,plain,(
    ! [A_51] : r1_tarski(k1_xboole_0,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_52])).

tff(c_409,plain,(
    ! [A_51] : k4_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_198,c_388])).

tff(c_997,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(k4_xboole_0(A_104,C_105),k4_xboole_0(B_106,C_105))
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5786,plain,(
    ! [A_222,C_223,B_224] :
      ( k4_xboole_0(k4_xboole_0(A_222,C_223),k4_xboole_0(B_224,C_223)) = k1_xboole_0
      | ~ r1_tarski(A_222,B_224) ) ),
    inference(resolution,[status(thm)],[c_997,c_36])).

tff(c_5927,plain,(
    ! [A_222,A_51] :
      ( k4_xboole_0(k4_xboole_0(A_222,A_51),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_222,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_5786])).

tff(c_5992,plain,(
    ! [A_225,A_226] :
      ( k4_xboole_0(A_225,A_226) = k1_xboole_0
      | ~ r1_tarski(A_225,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_5927])).

tff(c_6012,plain,(
    ! [A_18,A_226] :
      ( k4_xboole_0(A_18,A_226) = k1_xboole_0
      | k4_xboole_0(A_18,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_5992])).

tff(c_6043,plain,(
    ! [A_227,A_228] :
      ( k4_xboole_0(A_227,A_228) = k1_xboole_0
      | k1_xboole_0 != A_227 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_6012])).

tff(c_6125,plain,(
    ! [A_228,A_227] :
      ( k2_xboole_0(A_228,k1_xboole_0) = k2_xboole_0(A_228,A_227)
      | k1_xboole_0 != A_227 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6043,c_50])).

tff(c_6219,plain,(
    ! [A_228] : k2_xboole_0(A_228,k1_xboole_0) = A_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6125])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_837,plain,(
    ! [D_90,B_91,A_92] :
      ( ~ r2_hidden(D_90,B_91)
      | ~ r2_hidden(D_90,k4_xboole_0(A_92,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9945,plain,(
    ! [A_291,B_292,B_293] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_291,B_292),B_293),B_292)
      | r1_xboole_0(k4_xboole_0(A_291,B_292),B_293) ) ),
    inference(resolution,[status(thm)],[c_32,c_837])).

tff(c_9997,plain,(
    ! [A_294,B_295] : r1_xboole_0(k4_xboole_0(A_294,B_295),B_295) ),
    inference(resolution,[status(thm)],[c_30,c_9945])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10058,plain,(
    ! [A_298,B_299] : k3_xboole_0(k4_xboole_0(A_298,B_299),B_299) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9997,c_24])).

tff(c_10146,plain,(
    ! [B_299,A_298] : k3_xboole_0(B_299,k4_xboole_0(A_298,B_299)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10058,c_4])).

tff(c_1348,plain,(
    ! [A_120,B_121,C_122] : k3_xboole_0(k2_xboole_0(A_120,B_121),k2_xboole_0(A_120,C_122)) = k2_xboole_0(A_120,k3_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8102,plain,(
    ! [B_252,B_253,A_254] : k3_xboole_0(k2_xboole_0(B_252,B_253),k2_xboole_0(A_254,B_252)) = k2_xboole_0(B_252,k3_xboole_0(B_253,A_254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1348])).

tff(c_1651,plain,(
    ! [A_129,B_130,C_131] : k2_xboole_0(k3_xboole_0(A_129,B_130),k3_xboole_0(A_129,C_131)) = k3_xboole_0(A_129,k2_xboole_0(B_130,C_131)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1703,plain,(
    ! [A_129,B_130,C_131] : r1_tarski(k3_xboole_0(A_129,B_130),k3_xboole_0(A_129,k2_xboole_0(B_130,C_131))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1651,c_52])).

tff(c_77153,plain,(
    ! [B_767,B_768,A_769] : r1_tarski(k3_xboole_0(k2_xboole_0(B_767,B_768),A_769),k2_xboole_0(B_767,k3_xboole_0(B_768,A_769))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8102,c_1703])).

tff(c_77536,plain,(
    ! [B_767,B_299,A_298] : r1_tarski(k3_xboole_0(k2_xboole_0(B_767,B_299),k4_xboole_0(A_298,B_299)),k2_xboole_0(B_767,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10146,c_77153])).

tff(c_164356,plain,(
    ! [B_1159,B_1160,A_1161] : r1_tarski(k3_xboole_0(k2_xboole_0(B_1159,B_1160),k4_xboole_0(A_1161,B_1160)),B_1159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6219,c_77536])).

tff(c_164894,plain,(
    ! [B_1162,B_1163] : r1_tarski(k4_xboole_0(k2_xboole_0(B_1162,B_1163),B_1163),B_1162) ),
    inference(superposition,[status(thm),theory(equality)],[c_2869,c_164356])).

tff(c_46,plain,(
    ! [A_29,C_31,B_30] :
      ( r1_tarski(k4_xboole_0(A_29,C_31),k4_xboole_0(B_30,C_31))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5917,plain,(
    ! [A_222,A_32,B_33] :
      ( k4_xboole_0(k4_xboole_0(A_222,A_32),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_222,k4_xboole_0(A_32,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_5786])).

tff(c_53133,plain,(
    ! [A_634,A_635,B_636] :
      ( k4_xboole_0(A_634,A_635) = k1_xboole_0
      | ~ r1_tarski(A_634,k4_xboole_0(A_635,B_636)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_5917])).

tff(c_116269,plain,(
    ! [A_932,C_933,B_934] :
      ( k4_xboole_0(k4_xboole_0(A_932,C_933),B_934) = k1_xboole_0
      | ~ r1_tarski(A_932,B_934) ) ),
    inference(resolution,[status(thm)],[c_46,c_53133])).

tff(c_116645,plain,(
    ! [B_934,A_932,C_933] :
      ( k2_xboole_0(B_934,k4_xboole_0(A_932,C_933)) = k2_xboole_0(B_934,k1_xboole_0)
      | ~ r1_tarski(A_932,B_934) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116269,c_50])).

tff(c_157211,plain,(
    ! [B_1118,A_1119,C_1120] :
      ( k2_xboole_0(B_1118,k4_xboole_0(A_1119,C_1120)) = B_1118
      | ~ r1_tarski(A_1119,B_1118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6219,c_116645])).

tff(c_157910,plain,(
    ! [C_1120,A_1119] :
      ( k2_xboole_0(C_1120,A_1119) = C_1120
      | ~ r1_tarski(A_1119,C_1120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157211,c_50])).

tff(c_166568,plain,(
    ! [B_1168,B_1169] : k2_xboole_0(B_1168,k4_xboole_0(k2_xboole_0(B_1168,B_1169),B_1169)) = B_1168 ),
    inference(resolution,[status(thm)],[c_164894,c_157910])).

tff(c_4167,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4025])).

tff(c_167013,plain,(
    ! [B_1168,B_1169] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_1168,B_1169),B_1169),B_1168) = k2_xboole_0(B_1168,B_1168) ),
    inference(superposition,[status(thm),theory(equality)],[c_166568,c_4167])).

tff(c_171052,plain,(
    ! [B_1178,B_1179] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_1178,B_1179),B_1179),B_1178) = B_1178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_167013])).

tff(c_5849,plain,(
    ! [B_224,C_223,A_222] :
      ( k2_xboole_0(k4_xboole_0(B_224,C_223),k4_xboole_0(A_222,C_223)) = k2_xboole_0(k4_xboole_0(B_224,C_223),k1_xboole_0)
      | ~ r1_tarski(A_222,B_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5786,c_50])).

tff(c_5955,plain,(
    ! [B_224,C_223,A_222] :
      ( k2_xboole_0(k4_xboole_0(B_224,C_223),k4_xboole_0(A_222,C_223)) = k4_xboole_0(B_224,C_223)
      | ~ r1_tarski(A_222,B_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5849])).

tff(c_171109,plain,(
    ! [A_222,B_1179] :
      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(A_222,B_1179),B_1179),B_1179) = k4_xboole_0(A_222,B_1179)
      | ~ r1_tarski(A_222,k2_xboole_0(k4_xboole_0(A_222,B_1179),B_1179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171052,c_5955])).

tff(c_178361,plain,(
    ! [B_1197,A_1198] : k4_xboole_0(k2_xboole_0(B_1197,A_1198),B_1197) = k4_xboole_0(A_1198,B_1197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_29447,c_29447,c_171109])).

tff(c_179073,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178361])).

tff(c_54,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_5') != k4_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_180594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179073,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:58:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.13/35.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.13/35.48  
% 45.13/35.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.13/35.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 45.13/35.48  
% 45.13/35.48  %Foreground sorts:
% 45.13/35.48  
% 45.13/35.48  
% 45.13/35.48  %Background operators:
% 45.13/35.48  
% 45.13/35.48  
% 45.13/35.48  %Foreground operators:
% 45.13/35.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 45.13/35.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.13/35.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 45.13/35.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 45.13/35.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 45.13/35.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 45.13/35.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 45.13/35.48  tff('#skF_5', type, '#skF_5': $i).
% 45.13/35.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 45.13/35.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 45.13/35.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.13/35.48  tff('#skF_4', type, '#skF_4': $i).
% 45.13/35.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.13/35.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.13/35.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 45.13/35.48  
% 45.26/35.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 45.26/35.51  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 45.26/35.51  tff(f_67, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 45.26/35.51  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 45.26/35.51  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 45.26/35.51  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 45.26/35.51  tff(f_79, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 45.26/35.51  tff(f_69, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 45.26/35.51  tff(f_77, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 45.26/35.51  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 45.26/35.51  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 45.26/35.51  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 45.26/35.51  tff(f_73, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 45.26/35.51  tff(f_71, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 45.26/35.51  tff(f_86, negated_conjecture, ~(![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 45.26/35.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.26/35.51  tff(c_124, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 45.26/35.51  tff(c_52, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 45.26/35.51  tff(c_145, plain, (![A_50, B_49]: (r1_tarski(A_50, k2_xboole_0(B_49, A_50)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_52])).
% 45.26/35.51  tff(c_38, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_67])).
% 45.26/35.51  tff(c_388, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.26/35.51  tff(c_412, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_388])).
% 45.26/35.51  tff(c_593, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_81])).
% 45.26/35.51  tff(c_627, plain, (![A_36, B_37]: (k2_xboole_0(k2_xboole_0(A_36, B_37), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_412, c_593])).
% 45.26/35.51  tff(c_1046, plain, (![A_107, B_108]: (k2_xboole_0(k2_xboole_0(A_107, B_108), A_107)=k2_xboole_0(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_627])).
% 45.26/35.51  tff(c_1111, plain, (![B_2, B_108]: (k2_xboole_0(B_2, k2_xboole_0(B_2, B_108))=k2_xboole_0(B_2, B_108))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1046])).
% 45.26/35.51  tff(c_50, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 45.26/35.51  tff(c_407, plain, (![A_50, B_49]: (k4_xboole_0(A_50, k2_xboole_0(B_49, A_50))=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_388])).
% 45.26/35.51  tff(c_624, plain, (![B_49, A_50]: (k2_xboole_0(k2_xboole_0(B_49, A_50), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_407, c_593])).
% 45.26/35.51  tff(c_3632, plain, (![B_188, A_189]: (k2_xboole_0(k2_xboole_0(B_188, A_189), A_189)=k2_xboole_0(B_188, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_624])).
% 45.26/35.51  tff(c_4025, plain, (![A_195, B_196]: (k2_xboole_0(A_195, k2_xboole_0(B_196, A_195))=k2_xboole_0(B_196, A_195))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3632])).
% 45.26/35.51  tff(c_29008, plain, (![B_474, A_475]: (k2_xboole_0(B_474, k2_xboole_0(B_474, A_475))=k2_xboole_0(A_475, B_474))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4025])).
% 45.26/35.51  tff(c_29360, plain, (![B_35, A_34]: (k2_xboole_0(k4_xboole_0(B_35, A_34), A_34)=k2_xboole_0(A_34, k2_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_29008])).
% 45.26/35.51  tff(c_29447, plain, (![B_35, A_34]: (k2_xboole_0(k4_xboole_0(B_35, A_34), A_34)=k2_xboole_0(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_1111, c_29360])).
% 45.26/35.51  tff(c_64, plain, (![A_39, B_40]: (r1_tarski(A_39, k2_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 45.26/35.51  tff(c_67, plain, (![A_20]: (r1_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_38, c_64])).
% 45.26/35.51  tff(c_411, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_388])).
% 45.26/35.51  tff(c_636, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_411, c_593])).
% 45.26/35.51  tff(c_651, plain, (![A_20]: (k2_xboole_0(A_20, A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_636])).
% 45.26/35.51  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 45.26/35.51  tff(c_48, plain, (![A_32, B_33]: (r1_tarski(k4_xboole_0(A_32, B_33), A_32))), inference(cnfTransformation, [status(thm)], [f_79])).
% 45.26/35.51  tff(c_410, plain, (![A_32, B_33]: (k4_xboole_0(k4_xboole_0(A_32, B_33), A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_388])).
% 45.26/35.51  tff(c_630, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k2_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_410, c_593])).
% 45.26/35.51  tff(c_761, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_630])).
% 45.26/35.51  tff(c_40, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k2_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_69])).
% 45.26/35.51  tff(c_142, plain, (![B_49, A_50]: (k3_xboole_0(B_49, k2_xboole_0(A_50, B_49))=B_49)), inference(superposition, [status(thm), theory('equality')], [c_124, c_40])).
% 45.26/35.51  tff(c_2794, plain, (![A_162, B_163]: (k3_xboole_0(k4_xboole_0(A_162, B_163), A_162)=k4_xboole_0(A_162, B_163))), inference(superposition, [status(thm), theory('equality')], [c_761, c_142])).
% 45.26/35.51  tff(c_2869, plain, (![B_4, B_163]: (k3_xboole_0(B_4, k4_xboole_0(B_4, B_163))=k4_xboole_0(B_4, B_163))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2794])).
% 45.26/35.51  tff(c_152, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_124, c_38])).
% 45.26/35.51  tff(c_612, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_593, c_152])).
% 45.26/35.51  tff(c_643, plain, (![B_85]: (k4_xboole_0(B_85, k1_xboole_0)=B_85)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_612])).
% 45.26/35.51  tff(c_34, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.26/35.51  tff(c_183, plain, (![A_51]: (k2_xboole_0(k1_xboole_0, A_51)=A_51)), inference(superposition, [status(thm), theory('equality')], [c_124, c_38])).
% 45.26/35.51  tff(c_198, plain, (![A_51]: (r1_tarski(k1_xboole_0, A_51))), inference(superposition, [status(thm), theory('equality')], [c_183, c_52])).
% 45.26/35.51  tff(c_409, plain, (![A_51]: (k4_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_198, c_388])).
% 45.26/35.51  tff(c_997, plain, (![A_104, C_105, B_106]: (r1_tarski(k4_xboole_0(A_104, C_105), k4_xboole_0(B_106, C_105)) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_77])).
% 45.26/35.51  tff(c_36, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 45.26/35.51  tff(c_5786, plain, (![A_222, C_223, B_224]: (k4_xboole_0(k4_xboole_0(A_222, C_223), k4_xboole_0(B_224, C_223))=k1_xboole_0 | ~r1_tarski(A_222, B_224))), inference(resolution, [status(thm)], [c_997, c_36])).
% 45.26/35.51  tff(c_5927, plain, (![A_222, A_51]: (k4_xboole_0(k4_xboole_0(A_222, A_51), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_222, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_5786])).
% 45.26/35.51  tff(c_5992, plain, (![A_225, A_226]: (k4_xboole_0(A_225, A_226)=k1_xboole_0 | ~r1_tarski(A_225, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_5927])).
% 45.26/35.51  tff(c_6012, plain, (![A_18, A_226]: (k4_xboole_0(A_18, A_226)=k1_xboole_0 | k4_xboole_0(A_18, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_5992])).
% 45.26/35.51  tff(c_6043, plain, (![A_227, A_228]: (k4_xboole_0(A_227, A_228)=k1_xboole_0 | k1_xboole_0!=A_227)), inference(demodulation, [status(thm), theory('equality')], [c_643, c_6012])).
% 45.26/35.51  tff(c_6125, plain, (![A_228, A_227]: (k2_xboole_0(A_228, k1_xboole_0)=k2_xboole_0(A_228, A_227) | k1_xboole_0!=A_227)), inference(superposition, [status(thm), theory('equality')], [c_6043, c_50])).
% 45.26/35.51  tff(c_6219, plain, (![A_228]: (k2_xboole_0(A_228, k1_xboole_0)=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6125])).
% 45.26/35.51  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.26/35.51  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 45.26/35.51  tff(c_837, plain, (![D_90, B_91, A_92]: (~r2_hidden(D_90, B_91) | ~r2_hidden(D_90, k4_xboole_0(A_92, B_91)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 45.26/35.51  tff(c_9945, plain, (![A_291, B_292, B_293]: (~r2_hidden('#skF_3'(k4_xboole_0(A_291, B_292), B_293), B_292) | r1_xboole_0(k4_xboole_0(A_291, B_292), B_293))), inference(resolution, [status(thm)], [c_32, c_837])).
% 45.26/35.51  tff(c_9997, plain, (![A_294, B_295]: (r1_xboole_0(k4_xboole_0(A_294, B_295), B_295))), inference(resolution, [status(thm)], [c_30, c_9945])).
% 45.26/35.51  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 45.26/35.51  tff(c_10058, plain, (![A_298, B_299]: (k3_xboole_0(k4_xboole_0(A_298, B_299), B_299)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9997, c_24])).
% 45.26/35.51  tff(c_10146, plain, (![B_299, A_298]: (k3_xboole_0(B_299, k4_xboole_0(A_298, B_299))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10058, c_4])).
% 45.26/35.51  tff(c_1348, plain, (![A_120, B_121, C_122]: (k3_xboole_0(k2_xboole_0(A_120, B_121), k2_xboole_0(A_120, C_122))=k2_xboole_0(A_120, k3_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 45.26/35.51  tff(c_8102, plain, (![B_252, B_253, A_254]: (k3_xboole_0(k2_xboole_0(B_252, B_253), k2_xboole_0(A_254, B_252))=k2_xboole_0(B_252, k3_xboole_0(B_253, A_254)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1348])).
% 45.26/35.51  tff(c_1651, plain, (![A_129, B_130, C_131]: (k2_xboole_0(k3_xboole_0(A_129, B_130), k3_xboole_0(A_129, C_131))=k3_xboole_0(A_129, k2_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 45.26/35.51  tff(c_1703, plain, (![A_129, B_130, C_131]: (r1_tarski(k3_xboole_0(A_129, B_130), k3_xboole_0(A_129, k2_xboole_0(B_130, C_131))))), inference(superposition, [status(thm), theory('equality')], [c_1651, c_52])).
% 45.26/35.51  tff(c_77153, plain, (![B_767, B_768, A_769]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_767, B_768), A_769), k2_xboole_0(B_767, k3_xboole_0(B_768, A_769))))), inference(superposition, [status(thm), theory('equality')], [c_8102, c_1703])).
% 45.26/35.51  tff(c_77536, plain, (![B_767, B_299, A_298]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_767, B_299), k4_xboole_0(A_298, B_299)), k2_xboole_0(B_767, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10146, c_77153])).
% 45.26/35.51  tff(c_164356, plain, (![B_1159, B_1160, A_1161]: (r1_tarski(k3_xboole_0(k2_xboole_0(B_1159, B_1160), k4_xboole_0(A_1161, B_1160)), B_1159))), inference(demodulation, [status(thm), theory('equality')], [c_6219, c_77536])).
% 45.26/35.51  tff(c_164894, plain, (![B_1162, B_1163]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_1162, B_1163), B_1163), B_1162))), inference(superposition, [status(thm), theory('equality')], [c_2869, c_164356])).
% 45.26/35.51  tff(c_46, plain, (![A_29, C_31, B_30]: (r1_tarski(k4_xboole_0(A_29, C_31), k4_xboole_0(B_30, C_31)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 45.26/35.51  tff(c_5917, plain, (![A_222, A_32, B_33]: (k4_xboole_0(k4_xboole_0(A_222, A_32), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_222, k4_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_410, c_5786])).
% 45.26/35.51  tff(c_53133, plain, (![A_634, A_635, B_636]: (k4_xboole_0(A_634, A_635)=k1_xboole_0 | ~r1_tarski(A_634, k4_xboole_0(A_635, B_636)))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_5917])).
% 45.26/35.51  tff(c_116269, plain, (![A_932, C_933, B_934]: (k4_xboole_0(k4_xboole_0(A_932, C_933), B_934)=k1_xboole_0 | ~r1_tarski(A_932, B_934))), inference(resolution, [status(thm)], [c_46, c_53133])).
% 45.26/35.51  tff(c_116645, plain, (![B_934, A_932, C_933]: (k2_xboole_0(B_934, k4_xboole_0(A_932, C_933))=k2_xboole_0(B_934, k1_xboole_0) | ~r1_tarski(A_932, B_934))), inference(superposition, [status(thm), theory('equality')], [c_116269, c_50])).
% 45.26/35.51  tff(c_157211, plain, (![B_1118, A_1119, C_1120]: (k2_xboole_0(B_1118, k4_xboole_0(A_1119, C_1120))=B_1118 | ~r1_tarski(A_1119, B_1118))), inference(demodulation, [status(thm), theory('equality')], [c_6219, c_116645])).
% 45.26/35.51  tff(c_157910, plain, (![C_1120, A_1119]: (k2_xboole_0(C_1120, A_1119)=C_1120 | ~r1_tarski(A_1119, C_1120))), inference(superposition, [status(thm), theory('equality')], [c_157211, c_50])).
% 45.26/35.51  tff(c_166568, plain, (![B_1168, B_1169]: (k2_xboole_0(B_1168, k4_xboole_0(k2_xboole_0(B_1168, B_1169), B_1169))=B_1168)), inference(resolution, [status(thm)], [c_164894, c_157910])).
% 45.26/35.51  tff(c_4167, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4025])).
% 45.26/35.51  tff(c_167013, plain, (![B_1168, B_1169]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_1168, B_1169), B_1169), B_1168)=k2_xboole_0(B_1168, B_1168))), inference(superposition, [status(thm), theory('equality')], [c_166568, c_4167])).
% 45.26/35.51  tff(c_171052, plain, (![B_1178, B_1179]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_1178, B_1179), B_1179), B_1178)=B_1178)), inference(demodulation, [status(thm), theory('equality')], [c_651, c_167013])).
% 45.26/35.51  tff(c_5849, plain, (![B_224, C_223, A_222]: (k2_xboole_0(k4_xboole_0(B_224, C_223), k4_xboole_0(A_222, C_223))=k2_xboole_0(k4_xboole_0(B_224, C_223), k1_xboole_0) | ~r1_tarski(A_222, B_224))), inference(superposition, [status(thm), theory('equality')], [c_5786, c_50])).
% 45.26/35.51  tff(c_5955, plain, (![B_224, C_223, A_222]: (k2_xboole_0(k4_xboole_0(B_224, C_223), k4_xboole_0(A_222, C_223))=k4_xboole_0(B_224, C_223) | ~r1_tarski(A_222, B_224))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5849])).
% 45.26/35.51  tff(c_171109, plain, (![A_222, B_1179]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_222, B_1179), B_1179), B_1179)=k4_xboole_0(A_222, B_1179) | ~r1_tarski(A_222, k2_xboole_0(k4_xboole_0(A_222, B_1179), B_1179)))), inference(superposition, [status(thm), theory('equality')], [c_171052, c_5955])).
% 45.26/35.51  tff(c_178361, plain, (![B_1197, A_1198]: (k4_xboole_0(k2_xboole_0(B_1197, A_1198), B_1197)=k4_xboole_0(A_1198, B_1197))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_29447, c_29447, c_171109])).
% 45.26/35.51  tff(c_179073, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178361])).
% 45.26/35.51  tff(c_54, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_5')!=k4_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 45.26/35.51  tff(c_180594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179073, c_54])).
% 45.26/35.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 45.26/35.51  
% 45.26/35.51  Inference rules
% 45.26/35.51  ----------------------
% 45.26/35.51  #Ref     : 4
% 45.26/35.51  #Sup     : 48088
% 45.26/35.51  #Fact    : 0
% 45.26/35.51  #Define  : 0
% 45.26/35.51  #Split   : 3
% 45.26/35.51  #Chain   : 0
% 45.26/35.51  #Close   : 0
% 45.26/35.51  
% 45.26/35.51  Ordering : KBO
% 45.26/35.51  
% 45.26/35.51  Simplification rules
% 45.26/35.51  ----------------------
% 45.26/35.51  #Subsume      : 6254
% 45.26/35.51  #Demod        : 39615
% 45.26/35.51  #Tautology    : 23229
% 45.26/35.51  #SimpNegUnit  : 89
% 45.26/35.51  #BackRed      : 74
% 45.26/35.51  
% 45.26/35.51  #Partial instantiations: 0
% 45.26/35.51  #Strategies tried      : 1
% 45.26/35.51  
% 45.26/35.51  Timing (in seconds)
% 45.26/35.51  ----------------------
% 45.26/35.51  Preprocessing        : 0.29
% 45.26/35.51  Parsing              : 0.15
% 45.26/35.51  CNF conversion       : 0.02
% 45.26/35.51  Main loop            : 34.42
% 45.26/35.51  Inferencing          : 2.72
% 45.26/35.51  Reduction            : 22.78
% 45.26/35.51  Demodulation         : 21.26
% 45.26/35.51  BG Simplification    : 0.42
% 45.26/35.51  Subsumption          : 7.05
% 45.26/35.51  Abstraction          : 0.67
% 45.26/35.51  MUC search           : 0.00
% 45.26/35.51  Cooper               : 0.00
% 45.26/35.51  Total                : 34.75
% 45.26/35.51  Index Insertion      : 0.00
% 45.26/35.51  Index Deletion       : 0.00
% 45.26/35.51  Index Matching       : 0.00
% 45.26/35.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
