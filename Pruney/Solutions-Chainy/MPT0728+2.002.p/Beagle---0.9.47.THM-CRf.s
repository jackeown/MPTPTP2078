%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_32,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_tarski(A_17)) = k1_ordinal1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_107,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(B_31,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_116,plain,(
    ! [A_17] : r1_tarski(k1_tarski(A_17),k1_ordinal1(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_107])).

tff(c_37,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_14])).

tff(c_128,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | ~ r1_tarski(k1_tarski(A_41),B_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_128])).

tff(c_164,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(resolution,[status(thm)],[c_116,c_142])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4',k1_ordinal1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.16  
% 1.68/1.17  tff(f_49, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.68/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.68/1.17  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.68/1.17  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.68/1.17  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.68/1.17  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.17  tff(f_52, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.68/1.17  tff(c_32, plain, (![A_17]: (k2_xboole_0(A_17, k1_tarski(A_17))=k1_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.68/1.17  tff(c_68, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.17  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.68/1.17  tff(c_107, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(B_31, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_10])).
% 1.68/1.17  tff(c_116, plain, (![A_17]: (r1_tarski(k1_tarski(A_17), k1_ordinal1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_107])).
% 1.68/1.17  tff(c_37, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.17  tff(c_14, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.68/1.17  tff(c_43, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_14])).
% 1.68/1.17  tff(c_128, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.17  tff(c_142, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | ~r1_tarski(k1_tarski(A_41), B_42))), inference(resolution, [status(thm)], [c_43, c_128])).
% 1.68/1.17  tff(c_164, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(resolution, [status(thm)], [c_116, c_142])).
% 1.68/1.17  tff(c_34, plain, (~r2_hidden('#skF_4', k1_ordinal1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.68/1.17  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_34])).
% 1.68/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  Inference rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Ref     : 0
% 1.68/1.17  #Sup     : 30
% 1.68/1.17  #Fact    : 0
% 1.68/1.17  #Define  : 0
% 1.68/1.17  #Split   : 0
% 1.68/1.17  #Chain   : 0
% 1.68/1.17  #Close   : 0
% 1.68/1.17  
% 1.68/1.17  Ordering : KBO
% 1.68/1.17  
% 1.68/1.17  Simplification rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Subsume      : 0
% 1.68/1.17  #Demod        : 6
% 1.68/1.17  #Tautology    : 17
% 1.68/1.17  #SimpNegUnit  : 0
% 1.68/1.17  #BackRed      : 1
% 1.68/1.17  
% 1.68/1.17  #Partial instantiations: 0
% 1.68/1.17  #Strategies tried      : 1
% 1.68/1.17  
% 1.68/1.17  Timing (in seconds)
% 1.68/1.17  ----------------------
% 1.89/1.18  Preprocessing        : 0.28
% 1.89/1.18  Parsing              : 0.14
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.12
% 1.89/1.18  Inferencing          : 0.04
% 1.89/1.18  Reduction            : 0.04
% 1.89/1.18  Demodulation         : 0.03
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.02
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.42
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
