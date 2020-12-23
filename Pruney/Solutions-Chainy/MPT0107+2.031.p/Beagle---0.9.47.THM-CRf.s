%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  46 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = k2_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_94,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [B_27] : k3_xboole_0(k1_xboole_0,B_27) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_14])).

tff(c_195,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_165,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_351,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_165])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_234,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,k3_xboole_0(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_12])).

tff(c_550,plain,(
    ! [A_40,B_41] : k3_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_240])).

tff(c_259,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_234])).

tff(c_559,plain,(
    ! [A_40,B_41] : k4_xboole_0(k3_xboole_0(A_40,B_41),k3_xboole_0(A_40,B_41)) = k4_xboole_0(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_259])).

tff(c_603,plain,(
    ! [A_42,B_43] : k4_xboole_0(k3_xboole_0(A_42,B_43),A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_559])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_611,plain,(
    ! [A_42,B_43] : k2_xboole_0(k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)),k1_xboole_0) = k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_4])).

tff(c_648,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_94,c_611])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.41  
% 2.76/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.42  
% 2.76/1.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.76/1.43  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.76/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.76/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.43  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.76/1.43  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.76/1.43  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.76/1.43  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.76/1.43  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.43  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_78, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.43  tff(c_85, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=k2_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 2.76/1.43  tff(c_94, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85])).
% 2.76/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.43  tff(c_140, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.43  tff(c_14, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.43  tff(c_177, plain, (![B_27]: (k3_xboole_0(k1_xboole_0, B_27)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_14])).
% 2.76/1.43  tff(c_195, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 2.76/1.43  tff(c_165, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_140])).
% 2.76/1.43  tff(c_351, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_165])).
% 2.76/1.43  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.43  tff(c_234, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.43  tff(c_240, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, k3_xboole_0(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_12])).
% 2.76/1.43  tff(c_550, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_240])).
% 2.76/1.43  tff(c_259, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_234])).
% 2.76/1.43  tff(c_559, plain, (![A_40, B_41]: (k4_xboole_0(k3_xboole_0(A_40, B_41), k3_xboole_0(A_40, B_41))=k4_xboole_0(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_550, c_259])).
% 2.76/1.43  tff(c_603, plain, (![A_42, B_43]: (k4_xboole_0(k3_xboole_0(A_42, B_43), A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_351, c_559])).
% 2.76/1.43  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.43  tff(c_611, plain, (![A_42, B_43]: (k2_xboole_0(k4_xboole_0(A_42, k3_xboole_0(A_42, B_43)), k1_xboole_0)=k5_xboole_0(A_42, k3_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_603, c_4])).
% 2.76/1.43  tff(c_648, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_94, c_611])).
% 2.76/1.43  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.43  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_18])).
% 2.76/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.43  
% 2.76/1.43  Inference rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Ref     : 0
% 2.76/1.43  #Sup     : 408
% 2.76/1.43  #Fact    : 0
% 2.76/1.43  #Define  : 0
% 2.76/1.43  #Split   : 0
% 2.76/1.43  #Chain   : 0
% 2.76/1.43  #Close   : 0
% 2.76/1.43  
% 2.76/1.43  Ordering : KBO
% 2.76/1.43  
% 2.76/1.43  Simplification rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Subsume      : 0
% 2.76/1.43  #Demod        : 423
% 2.76/1.43  #Tautology    : 333
% 2.76/1.43  #SimpNegUnit  : 0
% 2.76/1.43  #BackRed      : 1
% 2.76/1.43  
% 2.76/1.43  #Partial instantiations: 0
% 2.76/1.43  #Strategies tried      : 1
% 2.76/1.43  
% 2.76/1.43  Timing (in seconds)
% 2.76/1.43  ----------------------
% 2.76/1.43  Preprocessing        : 0.27
% 2.76/1.43  Parsing              : 0.15
% 2.76/1.43  CNF conversion       : 0.01
% 2.76/1.43  Main loop            : 0.40
% 2.76/1.43  Inferencing          : 0.14
% 2.76/1.43  Reduction            : 0.18
% 2.76/1.43  Demodulation         : 0.15
% 2.76/1.43  BG Simplification    : 0.02
% 2.76/1.43  Subsumption          : 0.05
% 2.76/1.43  Abstraction          : 0.02
% 2.76/1.43  MUC search           : 0.00
% 2.76/1.43  Cooper               : 0.00
% 2.76/1.43  Total                : 0.69
% 2.76/1.43  Index Insertion      : 0.00
% 2.76/1.43  Index Deletion       : 0.00
% 2.76/1.43  Index Matching       : 0.00
% 2.76/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
