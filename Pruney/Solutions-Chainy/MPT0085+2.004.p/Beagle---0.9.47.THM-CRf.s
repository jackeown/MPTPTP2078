%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 12.99s
% Output     : CNFRefutation 12.99s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 342 expanded)
%              Number of leaves         :   22 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :   76 ( 373 expanded)
%              Number of equality atoms :   67 ( 339 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_161,plain,(
    ! [A_36,B_37] : k4_xboole_0(k2_xboole_0(A_36,B_37),B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_xboole_0) = k2_xboole_0(A_36,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_16])).

tff(c_186,plain,(
    ! [A_36] : k2_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_117,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_102])).

tff(c_120,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_189,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_206,plain,(
    ! [A_38,B_39,B_17] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(k4_xboole_0(A_38,B_39),B_17))) = k3_xboole_0(k4_xboole_0(A_38,B_39),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_3364,plain,(
    ! [A_111,B_112,B_113] : k4_xboole_0(A_111,k2_xboole_0(B_112,k4_xboole_0(A_111,k2_xboole_0(B_112,B_113)))) = k3_xboole_0(k4_xboole_0(A_111,B_112),B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_206])).

tff(c_3538,plain,(
    ! [B_112,B_113] : k4_xboole_0(k2_xboole_0(B_112,B_113),k2_xboole_0(B_112,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(k2_xboole_0(B_112,B_113),B_112),B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_3364])).

tff(c_3583,plain,(
    ! [B_113,B_112] : k3_xboole_0(k4_xboole_0(B_113,B_112),B_113) = k4_xboole_0(B_113,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_177,c_186,c_3538])).

tff(c_2378,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(A_95,k2_xboole_0(k4_xboole_0(A_95,B_96),C_97)) = k4_xboole_0(k3_xboole_0(A_95,B_96),C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_189])).

tff(c_18449,plain,(
    ! [A_245,A_246,B_247] : k4_xboole_0(A_245,k2_xboole_0(A_246,k4_xboole_0(A_245,B_247))) = k4_xboole_0(k3_xboole_0(A_245,B_247),A_246) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2378])).

tff(c_199,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_120])).

tff(c_18927,plain,(
    ! [A_248,B_249] : k4_xboole_0(k3_xboole_0(A_248,B_249),B_249) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18449,c_199])).

tff(c_19891,plain,(
    ! [B_252,B_253] : k4_xboole_0(k4_xboole_0(B_252,B_253),B_252) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3583,c_18927])).

tff(c_248,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_171])).

tff(c_276,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_286,plain,(
    ! [A_42] : k4_xboole_0(k1_xboole_0,A_42) = k4_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_18])).

tff(c_310,plain,(
    ! [A_42] : k4_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_286])).

tff(c_222,plain,(
    ! [A_10,C_40] : k4_xboole_0(A_10,k2_xboole_0(A_10,C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_189])).

tff(c_651,plain,(
    ! [A_54,C_55] : k4_xboole_0(A_54,k2_xboole_0(A_54,C_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_222])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_706,plain,(
    ! [A_54,C_55] : k2_xboole_0(A_54,k2_xboole_0(A_54,C_55)) = k2_xboole_0(A_54,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_651,c_96])).

tff(c_444,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | k4_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_447,plain,(
    ! [B_2,A_1] :
      ( k2_xboole_0(k2_xboole_0(B_2,A_1),B_2) = B_2
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_444])).

tff(c_466,plain,(
    ! [B_2,A_1] :
      ( k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = B_2
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_447])).

tff(c_7258,plain,(
    ! [B_2,A_1] :
      ( k2_xboole_0(B_2,A_1) = B_2
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_466])).

tff(c_20212,plain,(
    ! [B_252,B_253] : k2_xboole_0(B_252,k4_xboole_0(B_252,B_253)) = B_252 ),
    inference(superposition,[status(thm),theory(equality)],[c_19891,c_7258])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_585,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,k4_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_22])).

tff(c_628,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_585])).

tff(c_640,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_628])).

tff(c_19275,plain,(
    ! [A_250,B_251] : k2_xboole_0(k3_xboole_0(A_250,B_251),B_251) = B_251 ),
    inference(superposition,[status(thm),theory(equality)],[c_18927,c_96])).

tff(c_19632,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_19275])).

tff(c_21800,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20212,c_19632])).

tff(c_202,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),k4_xboole_0(A_38,k2_xboole_0(B_39,C_40))) = k3_xboole_0(k4_xboole_0(A_38,B_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_21883,plain,(
    ! [C_40] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_40))) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_21800,c_202])).

tff(c_39980,plain,(
    ! [C_349] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_349)) = k3_xboole_0('#skF_1',C_349) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21800,c_22,c_21883])).

tff(c_40202,plain,(
    ! [A_1] : k3_xboole_0('#skF_1',k2_xboole_0(A_1,'#skF_2')) = k3_xboole_0('#skF_1',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_39980])).

tff(c_24,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_45295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40202,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.33  % Computer   : n011.cluster.edu
% 0.15/0.33  % Model      : x86_64 x86_64
% 0.15/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.33  % Memory     : 8042.1875MB
% 0.15/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.33  % CPULimit   : 60
% 0.15/0.33  % DateTime   : Tue Dec  1 20:43:42 EST 2020
% 0.15/0.33  % CPUTime    : 
% 0.15/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.99/6.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.99/6.16  
% 12.99/6.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.99/6.17  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.99/6.17  
% 12.99/6.17  %Foreground sorts:
% 12.99/6.17  
% 12.99/6.17  
% 12.99/6.17  %Background operators:
% 12.99/6.17  
% 12.99/6.17  
% 12.99/6.17  %Foreground operators:
% 12.99/6.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.99/6.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.99/6.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.99/6.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.99/6.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.99/6.17  tff('#skF_2', type, '#skF_2': $i).
% 12.99/6.17  tff('#skF_3', type, '#skF_3': $i).
% 12.99/6.17  tff('#skF_1', type, '#skF_1': $i).
% 12.99/6.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.99/6.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.99/6.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.99/6.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.99/6.17  
% 12.99/6.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.99/6.18  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 12.99/6.18  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.99/6.18  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 12.99/6.18  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.99/6.18  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.99/6.18  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.99/6.18  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.99/6.18  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 12.99/6.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.99/6.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.99/6.18  tff(c_161, plain, (![A_36, B_37]: (k4_xboole_0(k2_xboole_0(A_36, B_37), B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.99/6.18  tff(c_177, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 12.99/6.18  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.99/6.18  tff(c_171, plain, (![A_36]: (k4_xboole_0(A_36, k1_xboole_0)=k2_xboole_0(A_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161, c_16])).
% 12.99/6.18  tff(c_186, plain, (![A_36]: (k2_xboole_0(A_36, k1_xboole_0)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_171])).
% 12.99/6.18  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.99/6.18  tff(c_102, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.99/6.18  tff(c_117, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_102])).
% 12.99/6.18  tff(c_120, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 12.99/6.18  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.99/6.18  tff(c_189, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.99/6.18  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.99/6.18  tff(c_206, plain, (![A_38, B_39, B_17]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(k4_xboole_0(A_38, B_39), B_17)))=k3_xboole_0(k4_xboole_0(A_38, B_39), B_17))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 12.99/6.18  tff(c_3364, plain, (![A_111, B_112, B_113]: (k4_xboole_0(A_111, k2_xboole_0(B_112, k4_xboole_0(A_111, k2_xboole_0(B_112, B_113))))=k3_xboole_0(k4_xboole_0(A_111, B_112), B_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_206])).
% 12.99/6.18  tff(c_3538, plain, (![B_112, B_113]: (k4_xboole_0(k2_xboole_0(B_112, B_113), k2_xboole_0(B_112, k1_xboole_0))=k3_xboole_0(k4_xboole_0(k2_xboole_0(B_112, B_113), B_112), B_113))), inference(superposition, [status(thm), theory('equality')], [c_120, c_3364])).
% 12.99/6.18  tff(c_3583, plain, (![B_113, B_112]: (k3_xboole_0(k4_xboole_0(B_113, B_112), B_113)=k4_xboole_0(B_113, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_177, c_186, c_3538])).
% 12.99/6.18  tff(c_2378, plain, (![A_95, B_96, C_97]: (k4_xboole_0(A_95, k2_xboole_0(k4_xboole_0(A_95, B_96), C_97))=k4_xboole_0(k3_xboole_0(A_95, B_96), C_97))), inference(superposition, [status(thm), theory('equality')], [c_22, c_189])).
% 12.99/6.18  tff(c_18449, plain, (![A_245, A_246, B_247]: (k4_xboole_0(A_245, k2_xboole_0(A_246, k4_xboole_0(A_245, B_247)))=k4_xboole_0(k3_xboole_0(A_245, B_247), A_246))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2378])).
% 12.99/6.18  tff(c_199, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_120])).
% 12.99/6.18  tff(c_18927, plain, (![A_248, B_249]: (k4_xboole_0(k3_xboole_0(A_248, B_249), B_249)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18449, c_199])).
% 12.99/6.18  tff(c_19891, plain, (![B_252, B_253]: (k4_xboole_0(k4_xboole_0(B_252, B_253), B_252)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3583, c_18927])).
% 12.99/6.18  tff(c_248, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_171])).
% 12.99/6.18  tff(c_276, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_248, c_2])).
% 12.99/6.18  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.99/6.18  tff(c_286, plain, (![A_42]: (k4_xboole_0(k1_xboole_0, A_42)=k4_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_276, c_18])).
% 12.99/6.18  tff(c_310, plain, (![A_42]: (k4_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_286])).
% 12.99/6.18  tff(c_222, plain, (![A_10, C_40]: (k4_xboole_0(A_10, k2_xboole_0(A_10, C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_120, c_189])).
% 12.99/6.18  tff(c_651, plain, (![A_54, C_55]: (k4_xboole_0(A_54, k2_xboole_0(A_54, C_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_222])).
% 12.99/6.18  tff(c_92, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.99/6.18  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.99/6.18  tff(c_96, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_12])).
% 12.99/6.18  tff(c_706, plain, (![A_54, C_55]: (k2_xboole_0(A_54, k2_xboole_0(A_54, C_55))=k2_xboole_0(A_54, C_55))), inference(superposition, [status(thm), theory('equality')], [c_651, c_96])).
% 12.99/6.18  tff(c_444, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | k4_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_12])).
% 12.99/6.18  tff(c_447, plain, (![B_2, A_1]: (k2_xboole_0(k2_xboole_0(B_2, A_1), B_2)=B_2 | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_177, c_444])).
% 12.99/6.18  tff(c_466, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=B_2 | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_447])).
% 12.99/6.18  tff(c_7258, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=B_2 | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_466])).
% 12.99/6.18  tff(c_20212, plain, (![B_252, B_253]: (k2_xboole_0(B_252, k4_xboole_0(B_252, B_253))=B_252)), inference(superposition, [status(thm), theory('equality')], [c_19891, c_7258])).
% 12.99/6.18  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.99/6.18  tff(c_79, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.99/6.18  tff(c_87, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_79])).
% 12.99/6.18  tff(c_585, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_22])).
% 12.99/6.18  tff(c_628, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_585])).
% 12.99/6.18  tff(c_640, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_628])).
% 12.99/6.18  tff(c_19275, plain, (![A_250, B_251]: (k2_xboole_0(k3_xboole_0(A_250, B_251), B_251)=B_251)), inference(superposition, [status(thm), theory('equality')], [c_18927, c_96])).
% 12.99/6.18  tff(c_19632, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_640, c_19275])).
% 12.99/6.18  tff(c_21800, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20212, c_19632])).
% 12.99/6.18  tff(c_202, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))=k3_xboole_0(k4_xboole_0(A_38, B_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 12.99/6.18  tff(c_21883, plain, (![C_40]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_40)))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), C_40))), inference(superposition, [status(thm), theory('equality')], [c_21800, c_202])).
% 12.99/6.18  tff(c_39980, plain, (![C_349]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_349))=k3_xboole_0('#skF_1', C_349))), inference(demodulation, [status(thm), theory('equality')], [c_21800, c_22, c_21883])).
% 12.99/6.18  tff(c_40202, plain, (![A_1]: (k3_xboole_0('#skF_1', k2_xboole_0(A_1, '#skF_2'))=k3_xboole_0('#skF_1', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_39980])).
% 12.99/6.18  tff(c_24, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.99/6.18  tff(c_27, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 12.99/6.18  tff(c_45295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40202, c_27])).
% 12.99/6.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.99/6.18  
% 12.99/6.18  Inference rules
% 12.99/6.18  ----------------------
% 12.99/6.18  #Ref     : 0
% 12.99/6.18  #Sup     : 11292
% 12.99/6.18  #Fact    : 0
% 12.99/6.18  #Define  : 0
% 12.99/6.18  #Split   : 1
% 12.99/6.18  #Chain   : 0
% 12.99/6.18  #Close   : 0
% 12.99/6.18  
% 12.99/6.18  Ordering : KBO
% 12.99/6.18  
% 12.99/6.18  Simplification rules
% 12.99/6.18  ----------------------
% 12.99/6.18  #Subsume      : 51
% 12.99/6.18  #Demod        : 13674
% 12.99/6.18  #Tautology    : 7511
% 12.99/6.18  #SimpNegUnit  : 0
% 12.99/6.18  #BackRed      : 4
% 12.99/6.18  
% 12.99/6.18  #Partial instantiations: 0
% 12.99/6.18  #Strategies tried      : 1
% 12.99/6.18  
% 12.99/6.18  Timing (in seconds)
% 12.99/6.18  ----------------------
% 12.99/6.18  Preprocessing        : 0.27
% 12.99/6.18  Parsing              : 0.15
% 12.99/6.18  CNF conversion       : 0.02
% 12.99/6.18  Main loop            : 5.15
% 12.99/6.18  Inferencing          : 0.89
% 12.99/6.18  Reduction            : 3.16
% 12.99/6.18  Demodulation         : 2.88
% 12.99/6.18  BG Simplification    : 0.11
% 12.99/6.18  Subsumption          : 0.80
% 12.99/6.18  Abstraction          : 0.20
% 12.99/6.18  MUC search           : 0.00
% 12.99/6.18  Cooper               : 0.00
% 12.99/6.18  Total                : 5.45
% 12.99/6.18  Index Insertion      : 0.00
% 12.99/6.18  Index Deletion       : 0.00
% 12.99/6.18  Index Matching       : 0.00
% 12.99/6.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
