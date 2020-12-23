%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_164])).

tff(c_546,plain,(
    ! [A_40,B_41] : k3_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_173])).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k3_xboole_0(A_4,B_5)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_616,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_6])).

tff(c_39,plain,(
    ! [B_18,A_19] : k2_xboole_0(B_18,A_19) = k2_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_19] : k2_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_310,plain,(
    ! [A_32,C_33,B_34] : k2_xboole_0(k4_xboole_0(A_32,C_33),k4_xboole_0(B_34,C_33)) = k4_xboole_0(k2_xboole_0(A_32,B_34),C_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_349,plain,(
    ! [B_34] : k4_xboole_0(k2_xboole_0('#skF_1',B_34),'#skF_2') = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_34,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_310])).

tff(c_363,plain,(
    ! [B_34] : k4_xboole_0(k2_xboole_0('#skF_1',B_34),'#skF_2') = k4_xboole_0(B_34,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_349])).

tff(c_623,plain,(
    ! [B_43] : k4_xboole_0(k4_xboole_0('#skF_1',B_43),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_363])).

tff(c_671,plain,(
    ! [B_43] : k4_xboole_0(k4_xboole_0('#skF_1',B_43),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_623])).

tff(c_141,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_149,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_141,c_18])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.39  
% 2.10/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.39  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.39  
% 2.10/1.39  %Foreground sorts:
% 2.10/1.39  
% 2.10/1.39  
% 2.10/1.39  %Background operators:
% 2.10/1.39  
% 2.10/1.39  
% 2.10/1.39  %Foreground operators:
% 2.10/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.39  
% 2.39/1.40  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.39/1.40  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.39/1.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.39/1.40  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.39/1.40  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.39/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.39/1.40  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.39/1.40  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.39/1.40  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.40  tff(c_86, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.40  tff(c_90, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.39/1.40  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.40  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.40  tff(c_164, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.40  tff(c_173, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_164])).
% 2.39/1.40  tff(c_546, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_173])).
% 2.39/1.40  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k3_xboole_0(A_4, B_5))=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.40  tff(c_616, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k4_xboole_0(A_42, B_43))=A_42)), inference(superposition, [status(thm), theory('equality')], [c_546, c_6])).
% 2.39/1.40  tff(c_39, plain, (![B_18, A_19]: (k2_xboole_0(B_18, A_19)=k2_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.40  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.40  tff(c_55, plain, (![A_19]: (k2_xboole_0(k1_xboole_0, A_19)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 2.39/1.40  tff(c_310, plain, (![A_32, C_33, B_34]: (k2_xboole_0(k4_xboole_0(A_32, C_33), k4_xboole_0(B_34, C_33))=k4_xboole_0(k2_xboole_0(A_32, B_34), C_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.40  tff(c_349, plain, (![B_34]: (k4_xboole_0(k2_xboole_0('#skF_1', B_34), '#skF_2')=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_34, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_310])).
% 2.39/1.40  tff(c_363, plain, (![B_34]: (k4_xboole_0(k2_xboole_0('#skF_1', B_34), '#skF_2')=k4_xboole_0(B_34, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_349])).
% 2.39/1.40  tff(c_623, plain, (![B_43]: (k4_xboole_0(k4_xboole_0('#skF_1', B_43), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_363])).
% 2.39/1.40  tff(c_671, plain, (![B_43]: (k4_xboole_0(k4_xboole_0('#skF_1', B_43), '#skF_2')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_623])).
% 2.39/1.40  tff(c_141, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.40  tff(c_18, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.40  tff(c_149, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_141, c_18])).
% 2.39/1.40  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_671, c_149])).
% 2.39/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.40  
% 2.39/1.40  Inference rules
% 2.39/1.40  ----------------------
% 2.39/1.40  #Ref     : 0
% 2.39/1.40  #Sup     : 167
% 2.39/1.40  #Fact    : 0
% 2.39/1.40  #Define  : 0
% 2.39/1.40  #Split   : 0
% 2.39/1.40  #Chain   : 0
% 2.39/1.40  #Close   : 0
% 2.39/1.40  
% 2.39/1.40  Ordering : KBO
% 2.39/1.40  
% 2.39/1.40  Simplification rules
% 2.39/1.40  ----------------------
% 2.39/1.40  #Subsume      : 4
% 2.39/1.40  #Demod        : 120
% 2.39/1.40  #Tautology    : 116
% 2.39/1.40  #SimpNegUnit  : 0
% 2.39/1.40  #BackRed      : 3
% 2.39/1.40  
% 2.39/1.40  #Partial instantiations: 0
% 2.39/1.40  #Strategies tried      : 1
% 2.39/1.40  
% 2.39/1.40  Timing (in seconds)
% 2.39/1.40  ----------------------
% 2.39/1.40  Preprocessing        : 0.28
% 2.39/1.40  Parsing              : 0.16
% 2.39/1.40  CNF conversion       : 0.02
% 2.39/1.40  Main loop            : 0.27
% 2.39/1.40  Inferencing          : 0.10
% 2.39/1.40  Reduction            : 0.10
% 2.39/1.40  Demodulation         : 0.08
% 2.39/1.40  BG Simplification    : 0.01
% 2.39/1.40  Subsumption          : 0.04
% 2.39/1.40  Abstraction          : 0.01
% 2.39/1.40  MUC search           : 0.00
% 2.39/1.41  Cooper               : 0.00
% 2.39/1.41  Total                : 0.58
% 2.39/1.41  Index Insertion      : 0.00
% 2.39/1.41  Index Deletion       : 0.00
% 2.39/1.41  Index Matching       : 0.00
% 2.39/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
