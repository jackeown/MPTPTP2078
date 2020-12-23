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
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 7.96s
% Output     : CNFRefutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  66 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_19,plain,(
    ! [B_14,A_15] : k3_xboole_0(B_14,A_15) = k3_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [B_14,A_15] : r1_tarski(k3_xboole_0(B_14,A_15),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_8])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(A_24,C_25)
      | ~ r1_xboole_0(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_220,plain,(
    ! [A_31,B_32,A_33] :
      ( r1_xboole_0(A_31,B_32)
      | ~ r1_tarski(A_31,A_33)
      | k3_xboole_0(A_33,B_32) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_587,plain,(
    ! [B_46,A_47,B_48] :
      ( r1_xboole_0(k3_xboole_0(B_46,A_47),B_48)
      | k3_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2109,plain,(
    ! [B_78,A_79,B_80] :
      ( k3_xboole_0(k3_xboole_0(B_78,A_79),B_80) = k1_xboole_0
      | k3_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_587,c_4])).

tff(c_12568,plain,(
    ! [B_181,B_182,A_183] :
      ( k3_xboole_0(B_181,k3_xboole_0(B_182,A_183)) = k1_xboole_0
      | k3_xboole_0(A_183,B_181) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2109])).

tff(c_510,plain,(
    ! [A_42,B_43,B_44] :
      ( r1_xboole_0(k3_xboole_0(A_42,B_43),B_44)
      | k3_xboole_0(A_42,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_14,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_553,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_510,c_17])).

tff(c_12854,plain,(
    k3_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12568,c_553])).

tff(c_13228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2,c_12854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.96/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/3.08  
% 7.96/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/3.08  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.96/3.08  
% 7.96/3.08  %Foreground sorts:
% 7.96/3.08  
% 7.96/3.08  
% 7.96/3.08  %Background operators:
% 7.96/3.08  
% 7.96/3.08  
% 7.96/3.08  %Foreground operators:
% 7.96/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.96/3.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.96/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.96/3.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.96/3.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.96/3.08  tff('#skF_2', type, '#skF_2': $i).
% 7.96/3.08  tff('#skF_3', type, '#skF_3': $i).
% 7.96/3.08  tff('#skF_1', type, '#skF_1': $i).
% 7.96/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.96/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.96/3.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.96/3.08  
% 7.96/3.09  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 7.96/3.09  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.96/3.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.96/3.09  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.96/3.09  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.96/3.09  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.96/3.09  tff(c_69, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.96/3.09  tff(c_77, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_69])).
% 7.96/3.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/3.09  tff(c_19, plain, (![B_14, A_15]: (k3_xboole_0(B_14, A_15)=k3_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.96/3.09  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.96/3.09  tff(c_34, plain, (![B_14, A_15]: (r1_tarski(k3_xboole_0(B_14, A_15), A_15))), inference(superposition, [status(thm), theory('equality')], [c_19, c_8])).
% 7.96/3.09  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.96/3.09  tff(c_107, plain, (![A_24, C_25, B_26]: (r1_xboole_0(A_24, C_25) | ~r1_xboole_0(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.96/3.09  tff(c_220, plain, (![A_31, B_32, A_33]: (r1_xboole_0(A_31, B_32) | ~r1_tarski(A_31, A_33) | k3_xboole_0(A_33, B_32)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_107])).
% 7.96/3.09  tff(c_587, plain, (![B_46, A_47, B_48]: (r1_xboole_0(k3_xboole_0(B_46, A_47), B_48) | k3_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_220])).
% 7.96/3.09  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.96/3.09  tff(c_2109, plain, (![B_78, A_79, B_80]: (k3_xboole_0(k3_xboole_0(B_78, A_79), B_80)=k1_xboole_0 | k3_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_587, c_4])).
% 7.96/3.09  tff(c_12568, plain, (![B_181, B_182, A_183]: (k3_xboole_0(B_181, k3_xboole_0(B_182, A_183))=k1_xboole_0 | k3_xboole_0(A_183, B_181)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2109])).
% 7.96/3.09  tff(c_510, plain, (![A_42, B_43, B_44]: (r1_xboole_0(k3_xboole_0(A_42, B_43), B_44) | k3_xboole_0(A_42, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_220])).
% 7.96/3.09  tff(c_14, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.96/3.09  tff(c_17, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 7.96/3.09  tff(c_553, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_510, c_17])).
% 7.96/3.09  tff(c_12854, plain, (k3_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12568, c_553])).
% 7.96/3.09  tff(c_13228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_2, c_12854])).
% 7.96/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.96/3.09  
% 7.96/3.09  Inference rules
% 7.96/3.09  ----------------------
% 7.96/3.09  #Ref     : 0
% 7.96/3.09  #Sup     : 3427
% 7.96/3.09  #Fact    : 0
% 7.96/3.09  #Define  : 0
% 7.96/3.09  #Split   : 6
% 7.96/3.09  #Chain   : 0
% 7.96/3.09  #Close   : 0
% 7.96/3.09  
% 7.96/3.09  Ordering : KBO
% 7.96/3.09  
% 7.96/3.09  Simplification rules
% 7.96/3.09  ----------------------
% 7.96/3.09  #Subsume      : 438
% 7.96/3.09  #Demod        : 2917
% 7.96/3.09  #Tautology    : 2067
% 7.96/3.09  #SimpNegUnit  : 12
% 7.96/3.09  #BackRed      : 8
% 7.96/3.09  
% 7.96/3.09  #Partial instantiations: 0
% 7.96/3.09  #Strategies tried      : 1
% 7.96/3.09  
% 7.96/3.09  Timing (in seconds)
% 7.96/3.09  ----------------------
% 7.96/3.09  Preprocessing        : 0.26
% 7.96/3.09  Parsing              : 0.15
% 7.96/3.09  CNF conversion       : 0.01
% 7.96/3.09  Main loop            : 2.00
% 7.96/3.09  Inferencing          : 0.46
% 7.96/3.09  Reduction            : 1.00
% 7.96/3.09  Demodulation         : 0.83
% 7.96/3.09  BG Simplification    : 0.05
% 7.96/3.09  Subsumption          : 0.37
% 7.96/3.09  Abstraction          : 0.06
% 7.96/3.09  MUC search           : 0.00
% 7.96/3.09  Cooper               : 0.00
% 7.96/3.09  Total                : 2.28
% 7.96/3.09  Index Insertion      : 0.00
% 7.96/3.09  Index Deletion       : 0.00
% 7.96/3.09  Index Matching       : 0.00
% 7.96/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
