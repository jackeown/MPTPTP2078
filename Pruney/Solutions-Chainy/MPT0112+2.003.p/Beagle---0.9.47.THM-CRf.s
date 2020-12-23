%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 134 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   59 ( 148 expanded)
%              Number of equality atoms :   47 ( 109 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_8,plain,(
    ! [B_6] : ~ r2_xboole_0(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_249,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_269,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_249])).

tff(c_272,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_269])).

tff(c_14,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_276,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_14])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_283,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_12])).

tff(c_95,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_18])).

tff(c_28,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ r2_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_182,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_94,c_182])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_417,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(B_50,A_49)) = k4_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_455,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_417])).

tff(c_475,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_455])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_481,plain,(
    ! [C_18] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_18)) = k5_xboole_0(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_22])).

tff(c_601,plain,(
    ! [C_53] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_53)) = C_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_481])).

tff(c_620,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_601])).

tff(c_204,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_191])).

tff(c_397,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_204])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_409,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_1')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_24])).

tff(c_1233,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_409])).

tff(c_217,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_191])).

tff(c_1237,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_217])).

tff(c_1243,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1237])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_484,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_4])).

tff(c_502,plain,(
    ! [C_18] : k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',C_18)) = k5_xboole_0(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_22])).

tff(c_646,plain,(
    ! [C_54] : k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',C_54)) = C_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_502])).

tff(c_684,plain,(
    ! [A_3] : k5_xboole_0('#skF_1',k5_xboole_0(A_3,'#skF_2')) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_646])).

tff(c_1251,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_684])).

tff(c_1261,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1251])).

tff(c_1280,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_28])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_1280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.53  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.53  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.53  
% 3.23/1.54  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.23/1.54  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.23/1.54  tff(f_61, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 3.23/1.54  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.23/1.54  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.23/1.54  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.54  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.23/1.54  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.54  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.23/1.54  tff(c_8, plain, (![B_6]: (~r2_xboole_0(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.54  tff(c_18, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.54  tff(c_26, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.54  tff(c_249, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.54  tff(c_269, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_249])).
% 3.23/1.54  tff(c_272, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_269])).
% 3.23/1.54  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.54  tff(c_276, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_272, c_14])).
% 3.23/1.54  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.54  tff(c_283, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_276, c_12])).
% 3.23/1.54  tff(c_95, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.54  tff(c_111, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_95, c_18])).
% 3.23/1.54  tff(c_28, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.54  tff(c_90, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~r2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.54  tff(c_94, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_90])).
% 3.23/1.54  tff(c_182, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.54  tff(c_186, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_94, c_182])).
% 3.23/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.54  tff(c_191, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.54  tff(c_417, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(B_50, A_49))=k4_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 3.23/1.54  tff(c_455, plain, (k5_xboole_0('#skF_2', '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_186, c_417])).
% 3.23/1.54  tff(c_475, plain, (k5_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_455])).
% 3.23/1.54  tff(c_22, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.54  tff(c_481, plain, (![C_18]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_18))=k5_xboole_0(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_475, c_22])).
% 3.23/1.54  tff(c_601, plain, (![C_53]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_53))=C_53)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_481])).
% 3.23/1.54  tff(c_620, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_283, c_601])).
% 3.23/1.54  tff(c_204, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_191])).
% 3.23/1.54  tff(c_397, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_204])).
% 3.23/1.54  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.54  tff(c_409, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_397, c_24])).
% 3.23/1.54  tff(c_1233, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_620, c_409])).
% 3.23/1.54  tff(c_217, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k5_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_191])).
% 3.23/1.54  tff(c_1237, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1233, c_217])).
% 3.23/1.54  tff(c_1243, plain, (k5_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1237])).
% 3.23/1.54  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.54  tff(c_484, plain, (k5_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_475, c_4])).
% 3.23/1.54  tff(c_502, plain, (![C_18]: (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', C_18))=k5_xboole_0(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_484, c_22])).
% 3.23/1.54  tff(c_646, plain, (![C_54]: (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', C_54))=C_54)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_502])).
% 3.23/1.54  tff(c_684, plain, (![A_3]: (k5_xboole_0('#skF_1', k5_xboole_0(A_3, '#skF_2'))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_646])).
% 3.23/1.54  tff(c_1251, plain, (k5_xboole_0('#skF_1', k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1243, c_684])).
% 3.23/1.54  tff(c_1261, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1251])).
% 3.23/1.54  tff(c_1280, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_28])).
% 3.23/1.54  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_1280])).
% 3.23/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  Inference rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Ref     : 0
% 3.23/1.54  #Sup     : 315
% 3.23/1.54  #Fact    : 0
% 3.23/1.54  #Define  : 0
% 3.23/1.54  #Split   : 0
% 3.23/1.54  #Chain   : 0
% 3.23/1.54  #Close   : 0
% 3.23/1.54  
% 3.23/1.54  Ordering : KBO
% 3.23/1.54  
% 3.23/1.54  Simplification rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Subsume      : 9
% 3.23/1.54  #Demod        : 157
% 3.23/1.54  #Tautology    : 183
% 3.23/1.54  #SimpNegUnit  : 1
% 3.23/1.54  #BackRed      : 16
% 3.23/1.54  
% 3.23/1.54  #Partial instantiations: 0
% 3.23/1.54  #Strategies tried      : 1
% 3.23/1.54  
% 3.23/1.54  Timing (in seconds)
% 3.23/1.54  ----------------------
% 3.23/1.55  Preprocessing        : 0.31
% 3.23/1.55  Parsing              : 0.17
% 3.23/1.55  CNF conversion       : 0.02
% 3.23/1.55  Main loop            : 0.43
% 3.23/1.55  Inferencing          : 0.15
% 3.23/1.55  Reduction            : 0.18
% 3.23/1.55  Demodulation         : 0.15
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.06
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.77
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
