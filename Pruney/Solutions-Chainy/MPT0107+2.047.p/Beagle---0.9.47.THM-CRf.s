%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  43 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_199,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_31,B_32] : k5_xboole_0(k4_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(k4_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_16])).

tff(c_690,plain,(
    ! [A_49,B_50] : k5_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_208])).

tff(c_46,plain,(
    ! [B_20,A_21] : k5_xboole_0(B_20,A_21) = k5_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_21] : k5_xboole_0(k1_xboole_0,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_37,B_38,C_39] : k5_xboole_0(k5_xboole_0(A_37,B_38),C_39) = k5_xboole_0(A_37,k5_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_306,plain,(
    ! [A_13,C_39] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_39)) = k5_xboole_0(k1_xboole_0,C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_242])).

tff(c_319,plain,(
    ! [A_13,C_39] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_39)) = C_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_306])).

tff(c_733,plain,(
    ! [A_51,B_52] : k5_xboole_0(k4_xboole_0(A_51,B_52),A_51) = k3_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_319])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_320,plain,(
    ! [A_40,C_41] : k5_xboole_0(A_40,k5_xboole_0(A_40,C_41)) = C_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_306])).

tff(c_363,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_745,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_363])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.42  
% 2.96/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.42  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.96/1.42  
% 2.96/1.42  %Foreground sorts:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Background operators:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Foreground operators:
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.42  
% 2.96/1.43  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.96/1.43  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.96/1.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.96/1.43  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.96/1.43  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.96/1.43  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.96/1.43  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.96/1.43  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.96/1.43  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.43  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.43  tff(c_140, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.43  tff(c_144, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.96/1.43  tff(c_199, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.43  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.43  tff(c_208, plain, (![A_31, B_32]: (k5_xboole_0(k4_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k2_xboole_0(k4_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_199, c_16])).
% 2.96/1.43  tff(c_690, plain, (![A_49, B_50]: (k5_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_208])).
% 2.96/1.43  tff(c_46, plain, (![B_20, A_21]: (k5_xboole_0(B_20, A_21)=k5_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.43  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.43  tff(c_62, plain, (![A_21]: (k5_xboole_0(k1_xboole_0, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_46, c_10])).
% 2.96/1.43  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.43  tff(c_242, plain, (![A_37, B_38, C_39]: (k5_xboole_0(k5_xboole_0(A_37, B_38), C_39)=k5_xboole_0(A_37, k5_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.43  tff(c_306, plain, (![A_13, C_39]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_39))=k5_xboole_0(k1_xboole_0, C_39))), inference(superposition, [status(thm), theory('equality')], [c_14, c_242])).
% 2.96/1.43  tff(c_319, plain, (![A_13, C_39]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_39))=C_39)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_306])).
% 2.96/1.43  tff(c_733, plain, (![A_51, B_52]: (k5_xboole_0(k4_xboole_0(A_51, B_52), A_51)=k3_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_690, c_319])).
% 2.96/1.43  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.43  tff(c_320, plain, (![A_40, C_41]: (k5_xboole_0(A_40, k5_xboole_0(A_40, C_41))=C_41)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_306])).
% 2.96/1.43  tff(c_363, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 2.96/1.43  tff(c_745, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_733, c_363])).
% 2.96/1.43  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.96/1.43  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_745, c_18])).
% 2.96/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.43  
% 2.96/1.43  Inference rules
% 2.96/1.43  ----------------------
% 2.96/1.43  #Ref     : 0
% 2.96/1.43  #Sup     : 337
% 2.96/1.44  #Fact    : 0
% 2.96/1.44  #Define  : 0
% 2.96/1.44  #Split   : 0
% 2.96/1.44  #Chain   : 0
% 2.96/1.44  #Close   : 0
% 2.96/1.44  
% 2.96/1.44  Ordering : KBO
% 2.96/1.44  
% 2.96/1.44  Simplification rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Subsume      : 6
% 2.96/1.44  #Demod        : 157
% 2.96/1.44  #Tautology    : 194
% 2.96/1.44  #SimpNegUnit  : 0
% 2.96/1.44  #BackRed      : 1
% 2.96/1.44  
% 2.96/1.44  #Partial instantiations: 0
% 2.96/1.44  #Strategies tried      : 1
% 2.96/1.44  
% 2.96/1.44  Timing (in seconds)
% 2.96/1.44  ----------------------
% 2.96/1.44  Preprocessing        : 0.26
% 2.96/1.44  Parsing              : 0.14
% 2.96/1.44  CNF conversion       : 0.01
% 2.96/1.44  Main loop            : 0.40
% 2.96/1.44  Inferencing          : 0.15
% 2.96/1.44  Reduction            : 0.16
% 2.96/1.44  Demodulation         : 0.13
% 2.96/1.44  BG Simplification    : 0.02
% 2.96/1.44  Subsumption          : 0.05
% 2.96/1.44  Abstraction          : 0.02
% 2.96/1.44  MUC search           : 0.00
% 2.96/1.44  Cooper               : 0.00
% 2.96/1.44  Total                : 0.69
% 2.96/1.44  Index Insertion      : 0.00
% 2.96/1.44  Index Deletion       : 0.00
% 2.96/1.44  Index Matching       : 0.00
% 2.96/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
