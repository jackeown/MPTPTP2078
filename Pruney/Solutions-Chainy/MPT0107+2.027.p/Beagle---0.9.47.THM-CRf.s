%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 328 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :   79 ( 405 expanded)
%              Number of equality atoms :   63 ( 308 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_142,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_142])).

tff(c_172,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_160])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_244,plain,(
    ! [A_42,B_43] : k3_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_160])).

tff(c_268,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_244])).

tff(c_276,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_268])).

tff(c_409,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k4_xboole_0(A_52,B_53),C_54) = k4_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_577,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k2_xboole_0(B_58,k1_xboole_0)) = k4_xboole_0(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_24])).

tff(c_611,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,k2_xboole_0(B_58,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_30])).

tff(c_641,plain,(
    ! [A_57,B_58] : k3_xboole_0(A_57,k2_xboole_0(B_58,k1_xboole_0)) = k3_xboole_0(A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_611])).

tff(c_1229,plain,(
    ! [A_85,B_86] : k3_xboole_0(A_85,k2_xboole_0(B_86,k1_xboole_0)) = k3_xboole_0(A_85,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_611])).

tff(c_1420,plain,(
    ! [B_92] : k3_xboole_0(k2_xboole_0(B_92,k1_xboole_0),B_92) = k2_xboole_0(B_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_276])).

tff(c_166,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k3_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_174,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_166])).

tff(c_1458,plain,(
    ! [B_92] : k3_xboole_0(k2_xboole_0(B_92,k1_xboole_0),k2_xboole_0(B_92,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(B_92,k1_xboole_0),B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_174])).

tff(c_1494,plain,(
    ! [B_92] : k2_xboole_0(B_92,k1_xboole_0) = B_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_641,c_276,c_2,c_1458])).

tff(c_32,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_142])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1218,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83,C_84),B_83)
      | r2_hidden('#skF_2'(A_82,B_83,C_84),C_84)
      | k4_xboole_0(A_82,B_83) = C_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1221,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_1218])).

tff(c_1226,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k3_xboole_0(A_3,k1_xboole_0) = C_5 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1221])).

tff(c_2152,plain,(
    ! [A_117,C_118] :
      ( r2_hidden('#skF_2'(A_117,A_117,C_118),C_118)
      | k3_xboole_0(A_117,k1_xboole_0) = C_118 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1221])).

tff(c_109,plain,(
    ! [D_27,B_28,A_29] :
      ( ~ r2_hidden(D_27,B_28)
      | ~ r2_hidden(D_27,k4_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [D_27,A_11] :
      ( ~ r2_hidden(D_27,k1_xboole_0)
      | ~ r2_hidden(D_27,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_2268,plain,(
    ! [A_122,A_123] :
      ( ~ r2_hidden('#skF_2'(A_122,A_122,k1_xboole_0),A_123)
      | k3_xboole_0(A_122,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2152,c_112])).

tff(c_2296,plain,(
    ! [A_124] : k3_xboole_0(A_124,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1226,c_2268])).

tff(c_113,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_2322,plain,(
    ! [A_124] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_131])).

tff(c_2357,plain,(
    ! [A_124] : k4_xboole_0(k1_xboole_0,A_124) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2322])).

tff(c_277,plain,(
    ! [A_44,B_45] : k2_xboole_0(k4_xboole_0(A_44,B_45),k4_xboole_0(B_45,A_44)) = k5_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_304,plain,(
    ! [A_11] : k2_xboole_0(A_11,k4_xboole_0(k1_xboole_0,A_11)) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_277])).

tff(c_2659,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_304])).

tff(c_2661,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_2659])).

tff(c_2285,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1226,c_2268])).

tff(c_2363,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2285,c_169])).

tff(c_2410,plain,(
    ! [A_125] : k5_xboole_0(A_125,k1_xboole_0) = k2_xboole_0(A_125,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_2363,c_32])).

tff(c_2797,plain,(
    ! [A_125] : k2_xboole_0(A_125,A_125) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_2410])).

tff(c_3829,plain,(
    ! [C_163,A_164,B_165] : k5_xboole_0(C_163,k4_xboole_0(A_164,k2_xboole_0(B_165,C_163))) = k2_xboole_0(C_163,k4_xboole_0(A_164,B_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_32])).

tff(c_3860,plain,(
    ! [A_125,A_164] : k5_xboole_0(A_125,k4_xboole_0(A_164,A_125)) = k2_xboole_0(A_125,k4_xboole_0(A_164,A_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2797,c_3829])).

tff(c_3896,plain,(
    ! [A_125,A_164] : k2_xboole_0(A_125,k4_xboole_0(A_164,A_125)) = k2_xboole_0(A_125,A_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3860])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2420,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,k4_xboole_0(A_12,B_13))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2363])).

tff(c_4009,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,A_12)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3896,c_2420])).

tff(c_292,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(k4_xboole_0(A_17,B_18),A_17)) = k5_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_277])).

tff(c_11801,plain,(
    ! [A_264,B_265] : k5_xboole_0(A_264,k4_xboole_0(A_264,B_265)) = k3_xboole_0(A_264,B_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1494,c_4009,c_26,c_292])).

tff(c_11920,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11801])).

tff(c_11967,plain,(
    ! [A_266,B_267] : k5_xboole_0(A_266,k3_xboole_0(A_266,B_267)) = k4_xboole_0(A_266,B_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_11920])).

tff(c_12068,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11967])).

tff(c_34,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_12650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12068,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.45  
% 6.60/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.45  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.60/2.45  
% 6.60/2.45  %Foreground sorts:
% 6.60/2.45  
% 6.60/2.45  
% 6.60/2.45  %Background operators:
% 6.60/2.45  
% 6.60/2.45  
% 6.60/2.45  %Foreground operators:
% 6.60/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.60/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.60/2.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.60/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.60/2.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.60/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.60/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.60/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.60/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.60/2.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.60/2.45  
% 6.60/2.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.60/2.47  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.60/2.47  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.60/2.47  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.60/2.47  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.60/2.47  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.60/2.47  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.60/2.47  tff(f_39, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 6.60/2.47  tff(f_52, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.60/2.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.60/2.47  tff(c_28, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.60/2.47  tff(c_30, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.60/2.47  tff(c_142, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.60/2.47  tff(c_160, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_142])).
% 6.60/2.47  tff(c_172, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_160])).
% 6.60/2.47  tff(c_24, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.60/2.47  tff(c_244, plain, (![A_42, B_43]: (k3_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_160])).
% 6.60/2.47  tff(c_268, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_244])).
% 6.60/2.47  tff(c_276, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_268])).
% 6.60/2.47  tff(c_409, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k4_xboole_0(A_52, B_53), C_54)=k4_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.60/2.47  tff(c_577, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k2_xboole_0(B_58, k1_xboole_0))=k4_xboole_0(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_409, c_24])).
% 6.60/2.47  tff(c_611, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, k2_xboole_0(B_58, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_30])).
% 6.60/2.47  tff(c_641, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k2_xboole_0(B_58, k1_xboole_0))=k3_xboole_0(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_611])).
% 6.60/2.47  tff(c_1229, plain, (![A_85, B_86]: (k3_xboole_0(A_85, k2_xboole_0(B_86, k1_xboole_0))=k3_xboole_0(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_611])).
% 6.60/2.47  tff(c_1420, plain, (![B_92]: (k3_xboole_0(k2_xboole_0(B_92, k1_xboole_0), B_92)=k2_xboole_0(B_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_276])).
% 6.60/2.47  tff(c_166, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k3_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_142])).
% 6.60/2.47  tff(c_174, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_166])).
% 6.60/2.47  tff(c_1458, plain, (![B_92]: (k3_xboole_0(k2_xboole_0(B_92, k1_xboole_0), k2_xboole_0(B_92, k1_xboole_0))=k3_xboole_0(k2_xboole_0(B_92, k1_xboole_0), B_92))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_174])).
% 6.60/2.47  tff(c_1494, plain, (![B_92]: (k2_xboole_0(B_92, k1_xboole_0)=B_92)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_641, c_276, c_2, c_1458])).
% 6.60/2.47  tff(c_32, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.60/2.47  tff(c_169, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_142])).
% 6.60/2.47  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.60/2.47  tff(c_1218, plain, (![A_82, B_83, C_84]: (~r2_hidden('#skF_1'(A_82, B_83, C_84), B_83) | r2_hidden('#skF_2'(A_82, B_83, C_84), C_84) | k4_xboole_0(A_82, B_83)=C_84)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.60/2.47  tff(c_1221, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_1218])).
% 6.60/2.47  tff(c_1226, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k3_xboole_0(A_3, k1_xboole_0)=C_5)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1221])).
% 6.60/2.47  tff(c_2152, plain, (![A_117, C_118]: (r2_hidden('#skF_2'(A_117, A_117, C_118), C_118) | k3_xboole_0(A_117, k1_xboole_0)=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1221])).
% 6.60/2.47  tff(c_109, plain, (![D_27, B_28, A_29]: (~r2_hidden(D_27, B_28) | ~r2_hidden(D_27, k4_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.60/2.47  tff(c_112, plain, (![D_27, A_11]: (~r2_hidden(D_27, k1_xboole_0) | ~r2_hidden(D_27, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_109])).
% 6.60/2.47  tff(c_2268, plain, (![A_122, A_123]: (~r2_hidden('#skF_2'(A_122, A_122, k1_xboole_0), A_123) | k3_xboole_0(A_122, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2152, c_112])).
% 6.60/2.47  tff(c_2296, plain, (![A_124]: (k3_xboole_0(A_124, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1226, c_2268])).
% 6.60/2.47  tff(c_113, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.60/2.47  tff(c_131, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 6.60/2.47  tff(c_2322, plain, (![A_124]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_124))), inference(superposition, [status(thm), theory('equality')], [c_2296, c_131])).
% 6.60/2.47  tff(c_2357, plain, (![A_124]: (k4_xboole_0(k1_xboole_0, A_124)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2322])).
% 6.60/2.47  tff(c_277, plain, (![A_44, B_45]: (k2_xboole_0(k4_xboole_0(A_44, B_45), k4_xboole_0(B_45, A_44))=k5_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.60/2.47  tff(c_304, plain, (![A_11]: (k2_xboole_0(A_11, k4_xboole_0(k1_xboole_0, A_11))=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_277])).
% 6.60/2.47  tff(c_2659, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_304])).
% 6.60/2.47  tff(c_2661, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_2659])).
% 6.60/2.47  tff(c_2285, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1226, c_2268])).
% 6.60/2.47  tff(c_2363, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2285, c_169])).
% 6.60/2.47  tff(c_2410, plain, (![A_125]: (k5_xboole_0(A_125, k1_xboole_0)=k2_xboole_0(A_125, A_125))), inference(superposition, [status(thm), theory('equality')], [c_2363, c_32])).
% 6.60/2.47  tff(c_2797, plain, (![A_125]: (k2_xboole_0(A_125, A_125)=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_2410])).
% 6.60/2.47  tff(c_3829, plain, (![C_163, A_164, B_165]: (k5_xboole_0(C_163, k4_xboole_0(A_164, k2_xboole_0(B_165, C_163)))=k2_xboole_0(C_163, k4_xboole_0(A_164, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_409, c_32])).
% 6.60/2.47  tff(c_3860, plain, (![A_125, A_164]: (k5_xboole_0(A_125, k4_xboole_0(A_164, A_125))=k2_xboole_0(A_125, k4_xboole_0(A_164, A_125)))), inference(superposition, [status(thm), theory('equality')], [c_2797, c_3829])).
% 6.60/2.47  tff(c_3896, plain, (![A_125, A_164]: (k2_xboole_0(A_125, k4_xboole_0(A_164, A_125))=k2_xboole_0(A_125, A_164))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3860])).
% 6.60/2.47  tff(c_26, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.60/2.47  tff(c_2420, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, k4_xboole_0(A_12, B_13)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_2363])).
% 6.60/2.47  tff(c_4009, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, A_12))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3896, c_2420])).
% 6.60/2.47  tff(c_292, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(k4_xboole_0(A_17, B_18), A_17))=k5_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_277])).
% 6.60/2.47  tff(c_11801, plain, (![A_264, B_265]: (k5_xboole_0(A_264, k4_xboole_0(A_264, B_265))=k3_xboole_0(A_264, B_265))), inference(demodulation, [status(thm), theory('equality')], [c_1494, c_4009, c_26, c_292])).
% 6.60/2.47  tff(c_11920, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11801])).
% 6.60/2.47  tff(c_11967, plain, (![A_266, B_267]: (k5_xboole_0(A_266, k3_xboole_0(A_266, B_267))=k4_xboole_0(A_266, B_267))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_11920])).
% 6.60/2.47  tff(c_12068, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11967])).
% 6.60/2.47  tff(c_34, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.60/2.47  tff(c_35, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 6.60/2.47  tff(c_12650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12068, c_35])).
% 6.60/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.60/2.47  
% 6.60/2.47  Inference rules
% 6.60/2.47  ----------------------
% 6.60/2.47  #Ref     : 0
% 6.60/2.47  #Sup     : 3132
% 6.60/2.47  #Fact    : 0
% 6.60/2.47  #Define  : 0
% 6.60/2.47  #Split   : 0
% 6.60/2.47  #Chain   : 0
% 6.60/2.47  #Close   : 0
% 6.60/2.47  
% 6.60/2.47  Ordering : KBO
% 6.60/2.47  
% 6.60/2.47  Simplification rules
% 6.60/2.47  ----------------------
% 6.60/2.47  #Subsume      : 204
% 6.60/2.47  #Demod        : 3323
% 6.60/2.47  #Tautology    : 2010
% 6.60/2.47  #SimpNegUnit  : 0
% 6.60/2.47  #BackRed      : 18
% 6.60/2.47  
% 6.60/2.47  #Partial instantiations: 0
% 6.60/2.47  #Strategies tried      : 1
% 6.60/2.47  
% 6.60/2.47  Timing (in seconds)
% 6.60/2.47  ----------------------
% 6.60/2.47  Preprocessing        : 0.27
% 6.60/2.47  Parsing              : 0.15
% 6.60/2.47  CNF conversion       : 0.02
% 6.60/2.47  Main loop            : 1.42
% 6.60/2.47  Inferencing          : 0.42
% 6.60/2.47  Reduction            : 0.65
% 6.60/2.47  Demodulation         : 0.55
% 6.60/2.47  BG Simplification    : 0.05
% 6.60/2.47  Subsumption          : 0.22
% 6.60/2.47  Abstraction          : 0.07
% 6.60/2.47  MUC search           : 0.00
% 6.60/2.47  Cooper               : 0.00
% 6.60/2.47  Total                : 1.73
% 6.60/2.47  Index Insertion      : 0.00
% 6.60/2.47  Index Deletion       : 0.00
% 6.60/2.47  Index Matching       : 0.00
% 6.60/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
