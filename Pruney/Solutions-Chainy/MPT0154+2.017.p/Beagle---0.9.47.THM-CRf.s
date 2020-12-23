%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  39 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_106,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),k1_tarski(B_41)) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [A_40,B_41] : k3_xboole_0(k1_tarski(A_40),k2_tarski(A_40,B_41)) = k1_tarski(A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_536,plain,(
    ! [A_99,B_100,B_101] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_99,B_100),B_101),A_99)
      | r1_tarski(k3_xboole_0(A_99,B_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_127,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_604,plain,(
    ! [A_105,B_106] : r1_tarski(k3_xboole_0(A_105,B_106),A_105) ),
    inference(resolution,[status(thm)],[c_536,c_6])).

tff(c_631,plain,(
    ! [B_107,A_108] : r1_tarski(k3_xboole_0(B_107,A_108),A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_604])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_758,plain,(
    ! [B_116,A_117] : k2_xboole_0(k3_xboole_0(B_116,A_117),A_117) = A_117 ),
    inference(resolution,[status(thm)],[c_631,c_30])).

tff(c_2874,plain,(
    ! [A_178,B_179] : k2_xboole_0(k1_tarski(A_178),k2_tarski(A_178,B_179)) = k2_tarski(A_178,B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_758])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k1_tarski(A_24),k2_tarski(B_25,C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2894,plain,(
    ! [A_178,B_179] : k1_enumset1(A_178,A_178,B_179) = k2_tarski(A_178,B_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_2874,c_38])).

tff(c_42,plain,(
    k1_enumset1('#skF_4','#skF_4','#skF_5') != k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.66  
% 3.95/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.66  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.95/1.66  
% 3.95/1.66  %Foreground sorts:
% 3.95/1.66  
% 3.95/1.66  
% 3.95/1.66  %Background operators:
% 3.95/1.66  
% 3.95/1.66  
% 3.95/1.66  %Foreground operators:
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.95/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.95/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.95/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.95/1.66  
% 3.95/1.67  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.95/1.67  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.95/1.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.95/1.67  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.95/1.67  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.95/1.67  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.95/1.67  tff(f_57, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.95/1.67  tff(f_62, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.95/1.67  tff(c_106, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(B_41))=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.95/1.67  tff(c_32, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/1.67  tff(c_112, plain, (![A_40, B_41]: (k3_xboole_0(k1_tarski(A_40), k2_tarski(A_40, B_41))=k1_tarski(A_40))), inference(superposition, [status(thm), theory('equality')], [c_106, c_32])).
% 3.95/1.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.67  tff(c_127, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.95/1.67  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.67  tff(c_536, plain, (![A_99, B_100, B_101]: (r2_hidden('#skF_1'(k3_xboole_0(A_99, B_100), B_101), A_99) | r1_tarski(k3_xboole_0(A_99, B_100), B_101))), inference(resolution, [status(thm)], [c_127, c_14])).
% 3.95/1.67  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.95/1.67  tff(c_604, plain, (![A_105, B_106]: (r1_tarski(k3_xboole_0(A_105, B_106), A_105))), inference(resolution, [status(thm)], [c_536, c_6])).
% 3.95/1.67  tff(c_631, plain, (![B_107, A_108]: (r1_tarski(k3_xboole_0(B_107, A_108), A_108))), inference(superposition, [status(thm), theory('equality')], [c_2, c_604])).
% 3.95/1.67  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.67  tff(c_758, plain, (![B_116, A_117]: (k2_xboole_0(k3_xboole_0(B_116, A_117), A_117)=A_117)), inference(resolution, [status(thm)], [c_631, c_30])).
% 3.95/1.67  tff(c_2874, plain, (![A_178, B_179]: (k2_xboole_0(k1_tarski(A_178), k2_tarski(A_178, B_179))=k2_tarski(A_178, B_179))), inference(superposition, [status(thm), theory('equality')], [c_112, c_758])).
% 3.95/1.67  tff(c_38, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(B_25, C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.67  tff(c_2894, plain, (![A_178, B_179]: (k1_enumset1(A_178, A_178, B_179)=k2_tarski(A_178, B_179))), inference(superposition, [status(thm), theory('equality')], [c_2874, c_38])).
% 3.95/1.67  tff(c_42, plain, (k1_enumset1('#skF_4', '#skF_4', '#skF_5')!=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.67  tff(c_2925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2894, c_42])).
% 3.95/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.67  
% 3.95/1.67  Inference rules
% 3.95/1.67  ----------------------
% 3.95/1.67  #Ref     : 0
% 3.95/1.67  #Sup     : 732
% 3.95/1.67  #Fact    : 0
% 3.95/1.67  #Define  : 0
% 3.95/1.67  #Split   : 0
% 3.95/1.67  #Chain   : 0
% 3.95/1.67  #Close   : 0
% 3.95/1.67  
% 3.95/1.67  Ordering : KBO
% 3.95/1.67  
% 3.95/1.67  Simplification rules
% 3.95/1.67  ----------------------
% 3.95/1.67  #Subsume      : 71
% 3.95/1.67  #Demod        : 617
% 3.95/1.67  #Tautology    : 439
% 3.95/1.67  #SimpNegUnit  : 0
% 3.95/1.67  #BackRed      : 1
% 3.95/1.67  
% 3.95/1.67  #Partial instantiations: 0
% 3.95/1.67  #Strategies tried      : 1
% 3.95/1.67  
% 3.95/1.67  Timing (in seconds)
% 3.95/1.67  ----------------------
% 3.95/1.67  Preprocessing        : 0.31
% 3.95/1.67  Parsing              : 0.16
% 3.95/1.67  CNF conversion       : 0.02
% 3.95/1.67  Main loop            : 0.64
% 3.95/1.68  Inferencing          : 0.21
% 3.95/1.68  Reduction            : 0.26
% 3.95/1.68  Demodulation         : 0.21
% 3.95/1.68  BG Simplification    : 0.03
% 3.95/1.68  Subsumption          : 0.10
% 3.95/1.68  Abstraction          : 0.03
% 3.95/1.68  MUC search           : 0.00
% 3.95/1.68  Cooper               : 0.00
% 3.95/1.68  Total                : 0.98
% 3.95/1.68  Index Insertion      : 0.00
% 3.95/1.68  Index Deletion       : 0.00
% 3.95/1.68  Index Matching       : 0.00
% 3.95/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
