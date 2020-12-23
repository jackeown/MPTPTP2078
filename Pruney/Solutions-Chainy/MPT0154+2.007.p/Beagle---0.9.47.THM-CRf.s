%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:05 EST 2020

% Result     : Theorem 10.51s
% Output     : CNFRefutation 10.51s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   51 ( 102 expanded)
%              Number of equality atoms :   46 (  97 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_96,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k1_tarski(A_20),k2_tarski(B_21,C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),k1_tarski(B_19)) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_197,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_207,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k5_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_207])).

tff(c_271,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_220])).

tff(c_282,plain,(
    ! [A_18,B_19] : k4_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_271])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_347,plain,(
    ! [A_51,B_52,C_53] : k5_xboole_0(k5_xboole_0(A_51,B_52),C_53) = k5_xboole_0(A_51,k5_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_422,plain,(
    ! [A_15,C_53] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_53)) = k5_xboole_0(k1_xboole_0,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_347])).

tff(c_436,plain,(
    ! [A_54,C_55] : k5_xboole_0(A_54,k5_xboole_0(A_54,C_55)) = C_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_422])).

tff(c_472,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_436])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1836,plain,(
    ! [B_99,A_100,B_101] : k5_xboole_0(B_99,k5_xboole_0(A_100,B_101)) = k5_xboole_0(A_100,k5_xboole_0(B_101,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_347])).

tff(c_2556,plain,(
    ! [A_109,B_110] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_109,B_110)) = k5_xboole_0(B_110,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1836])).

tff(c_2641,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_2556])).

tff(c_2713,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2641])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6206,plain,(
    ! [A_165,B_166,C_167] : k5_xboole_0(A_165,k5_xboole_0(k4_xboole_0(B_166,A_165),C_167)) = k5_xboole_0(k2_xboole_0(A_165,B_166),C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_347])).

tff(c_6300,plain,(
    ! [B_6,A_5] : k5_xboole_0(k2_xboole_0(B_6,A_5),A_5) = k5_xboole_0(B_6,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2713,c_6206])).

tff(c_14056,plain,(
    ! [B_227,A_228] : k5_xboole_0(k2_xboole_0(B_227,A_228),A_228) = k4_xboole_0(B_227,A_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_6300])).

tff(c_482,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_436])).

tff(c_504,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k5_xboole_0(B_57,A_56)) = B_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_436])).

tff(c_531,plain,(
    ! [B_4,A_3] : k5_xboole_0(k5_xboole_0(B_4,A_3),B_4) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_504])).

tff(c_19727,plain,(
    ! [B_258,A_259] : k5_xboole_0(k4_xboole_0(B_258,A_259),k2_xboole_0(B_258,A_259)) = A_259 ),
    inference(superposition,[status(thm),theory(equality)],[c_14056,c_531])).

tff(c_19873,plain,(
    ! [A_18,B_19] : k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19))) = k2_tarski(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_19727])).

tff(c_19918,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_22,c_19873])).

tff(c_26,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_19924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19918,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:14:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.51/4.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/4.64  
% 10.51/4.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/4.64  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.51/4.64  
% 10.51/4.64  %Foreground sorts:
% 10.51/4.64  
% 10.51/4.64  
% 10.51/4.64  %Background operators:
% 10.51/4.64  
% 10.51/4.64  
% 10.51/4.64  %Foreground operators:
% 10.51/4.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.51/4.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.51/4.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.51/4.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.51/4.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.51/4.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.51/4.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.51/4.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.51/4.64  tff('#skF_2', type, '#skF_2': $i).
% 10.51/4.64  tff('#skF_1', type, '#skF_1': $i).
% 10.51/4.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.51/4.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.51/4.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.51/4.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.51/4.64  
% 10.51/4.65  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.51/4.65  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.51/4.65  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 10.51/4.65  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 10.51/4.65  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.51/4.65  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.51/4.65  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.51/4.65  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.51/4.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.51/4.65  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.51/4.65  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.51/4.65  tff(f_54, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.51/4.65  tff(c_96, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.51/4.65  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.51/4.65  tff(c_112, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 10.51/4.65  tff(c_22, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k1_tarski(A_20), k2_tarski(B_21, C_22))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.51/4.65  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(B_19))=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.51/4.65  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.51/4.65  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.51/4.65  tff(c_193, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.51/4.65  tff(c_197, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_12, c_193])).
% 10.51/4.65  tff(c_207, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.51/4.65  tff(c_220, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k5_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_197, c_207])).
% 10.51/4.65  tff(c_271, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k2_xboole_0(A_46, B_47))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_220])).
% 10.51/4.65  tff(c_282, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_271])).
% 10.51/4.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.51/4.65  tff(c_230, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_207])).
% 10.51/4.65  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.51/4.65  tff(c_347, plain, (![A_51, B_52, C_53]: (k5_xboole_0(k5_xboole_0(A_51, B_52), C_53)=k5_xboole_0(A_51, k5_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.51/4.65  tff(c_422, plain, (![A_15, C_53]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_53))=k5_xboole_0(k1_xboole_0, C_53))), inference(superposition, [status(thm), theory('equality')], [c_16, c_347])).
% 10.51/4.65  tff(c_436, plain, (![A_54, C_55]: (k5_xboole_0(A_54, k5_xboole_0(A_54, C_55))=C_55)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_422])).
% 10.51/4.65  tff(c_472, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_436])).
% 10.51/4.65  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.51/4.66  tff(c_1836, plain, (![B_99, A_100, B_101]: (k5_xboole_0(B_99, k5_xboole_0(A_100, B_101))=k5_xboole_0(A_100, k5_xboole_0(B_101, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_347])).
% 10.51/4.66  tff(c_2556, plain, (![A_109, B_110]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_109, B_110))=k5_xboole_0(B_110, A_109))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1836])).
% 10.51/4.66  tff(c_2641, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_472, c_2556])).
% 10.51/4.66  tff(c_2713, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2641])).
% 10.51/4.66  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.51/4.66  tff(c_6206, plain, (![A_165, B_166, C_167]: (k5_xboole_0(A_165, k5_xboole_0(k4_xboole_0(B_166, A_165), C_167))=k5_xboole_0(k2_xboole_0(A_165, B_166), C_167))), inference(superposition, [status(thm), theory('equality')], [c_18, c_347])).
% 10.51/4.66  tff(c_6300, plain, (![B_6, A_5]: (k5_xboole_0(k2_xboole_0(B_6, A_5), A_5)=k5_xboole_0(B_6, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_2713, c_6206])).
% 10.51/4.66  tff(c_14056, plain, (![B_227, A_228]: (k5_xboole_0(k2_xboole_0(B_227, A_228), A_228)=k4_xboole_0(B_227, A_228))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_6300])).
% 10.51/4.66  tff(c_482, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_436])).
% 10.51/4.66  tff(c_504, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k5_xboole_0(B_57, A_56))=B_57)), inference(superposition, [status(thm), theory('equality')], [c_4, c_436])).
% 10.51/4.66  tff(c_531, plain, (![B_4, A_3]: (k5_xboole_0(k5_xboole_0(B_4, A_3), B_4)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_482, c_504])).
% 10.51/4.66  tff(c_19727, plain, (![B_258, A_259]: (k5_xboole_0(k4_xboole_0(B_258, A_259), k2_xboole_0(B_258, A_259))=A_259)), inference(superposition, [status(thm), theory('equality')], [c_14056, c_531])).
% 10.51/4.66  tff(c_19873, plain, (![A_18, B_19]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19)))=k2_tarski(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_282, c_19727])).
% 10.51/4.66  tff(c_19918, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_22, c_19873])).
% 10.51/4.66  tff(c_26, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.51/4.66  tff(c_19924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19918, c_26])).
% 10.51/4.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/4.66  
% 10.51/4.66  Inference rules
% 10.51/4.66  ----------------------
% 10.51/4.66  #Ref     : 0
% 10.51/4.66  #Sup     : 5036
% 10.51/4.66  #Fact    : 0
% 10.51/4.66  #Define  : 0
% 10.51/4.66  #Split   : 0
% 10.51/4.66  #Chain   : 0
% 10.51/4.66  #Close   : 0
% 10.51/4.66  
% 10.51/4.66  Ordering : KBO
% 10.51/4.66  
% 10.51/4.66  Simplification rules
% 10.51/4.66  ----------------------
% 10.51/4.66  #Subsume      : 259
% 10.51/4.66  #Demod        : 5132
% 10.51/4.66  #Tautology    : 2220
% 10.51/4.66  #SimpNegUnit  : 0
% 10.51/4.66  #BackRed      : 1
% 10.51/4.66  
% 10.51/4.66  #Partial instantiations: 0
% 10.51/4.66  #Strategies tried      : 1
% 10.51/4.66  
% 10.51/4.66  Timing (in seconds)
% 10.51/4.66  ----------------------
% 10.51/4.66  Preprocessing        : 0.31
% 10.51/4.66  Parsing              : 0.16
% 10.51/4.66  CNF conversion       : 0.02
% 10.51/4.66  Main loop            : 3.57
% 10.51/4.66  Inferencing          : 0.66
% 10.51/4.66  Reduction            : 2.26
% 10.51/4.66  Demodulation         : 2.10
% 10.51/4.66  BG Simplification    : 0.10
% 10.51/4.66  Subsumption          : 0.42
% 10.51/4.66  Abstraction          : 0.14
% 10.51/4.66  MUC search           : 0.00
% 10.51/4.66  Cooper               : 0.00
% 10.51/4.66  Total                : 3.91
% 10.51/4.66  Index Insertion      : 0.00
% 10.51/4.66  Index Deletion       : 0.00
% 10.51/4.66  Index Matching       : 0.00
% 10.51/4.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
