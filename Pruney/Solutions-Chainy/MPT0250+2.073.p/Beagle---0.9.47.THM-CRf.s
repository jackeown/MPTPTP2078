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
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 9.05s
% Output     : CNFRefutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [E_14,B_9,C_10] : r2_hidden(E_14,k1_enumset1(E_14,B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [A_77,B_78] : r2_hidden(A_77,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_20])).

tff(c_58,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,k3_tarski(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    ! [B_79,A_80] : r2_hidden(B_79,k2_tarski(A_80,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_16])).

tff(c_100,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_97])).

tff(c_165,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_188,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(A_98,B_99)
      | ~ r1_tarski(k1_tarski(A_98),B_99) ) ),
    inference(resolution,[status(thm)],[c_100,c_165])).

tff(c_230,plain,(
    ! [A_106,B_107] :
      ( r2_hidden(A_106,k3_tarski(B_107))
      | ~ r2_hidden(k1_tarski(A_106),B_107) ) ),
    inference(resolution,[status(thm)],[c_58,c_188])).

tff(c_234,plain,(
    ! [A_106,B_78] : r2_hidden(A_106,k3_tarski(k2_tarski(k1_tarski(A_106),B_78))) ),
    inference(resolution,[status(thm)],[c_91,c_230])).

tff(c_272,plain,(
    ! [A_111,B_112] : r2_hidden(A_111,k2_xboole_0(k1_tarski(A_111),B_112)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_234])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6340,plain,(
    ! [A_13754,B_13755,B_13756] :
      ( r2_hidden(A_13754,B_13755)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_13754),B_13756),B_13755) ) ),
    inference(resolution,[status(thm)],[c_272,c_2])).

tff(c_6365,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_6340])).

tff(c_6377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:58:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.05/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.09/3.29  
% 9.09/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.09/3.30  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.09/3.30  
% 9.09/3.30  %Foreground sorts:
% 9.09/3.30  
% 9.09/3.30  
% 9.09/3.30  %Background operators:
% 9.09/3.30  
% 9.09/3.30  
% 9.09/3.30  %Foreground operators:
% 9.09/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.09/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.09/3.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.09/3.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.09/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.09/3.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.09/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.09/3.30  tff('#skF_5', type, '#skF_5': $i).
% 9.09/3.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.09/3.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.09/3.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.09/3.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.09/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.09/3.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.09/3.30  tff('#skF_4', type, '#skF_4': $i).
% 9.09/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.09/3.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.09/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.09/3.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.09/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.09/3.30  
% 9.16/3.31  tff(f_84, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 9.16/3.31  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 9.16/3.31  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.16/3.31  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.16/3.31  tff(f_77, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 9.16/3.31  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.16/3.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.16/3.31  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.16/3.31  tff(c_64, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.16/3.31  tff(c_60, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.16/3.31  tff(c_79, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.16/3.31  tff(c_20, plain, (![E_14, B_9, C_10]: (r2_hidden(E_14, k1_enumset1(E_14, B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.16/3.31  tff(c_91, plain, (![A_77, B_78]: (r2_hidden(A_77, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_20])).
% 9.16/3.31  tff(c_58, plain, (![A_62, B_63]: (r1_tarski(A_62, k3_tarski(B_63)) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.16/3.31  tff(c_44, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.16/3.31  tff(c_16, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.16/3.31  tff(c_97, plain, (![B_79, A_80]: (r2_hidden(B_79, k2_tarski(A_80, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_16])).
% 9.16/3.31  tff(c_100, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_97])).
% 9.16/3.31  tff(c_165, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.16/3.31  tff(c_188, plain, (![A_98, B_99]: (r2_hidden(A_98, B_99) | ~r1_tarski(k1_tarski(A_98), B_99))), inference(resolution, [status(thm)], [c_100, c_165])).
% 9.16/3.31  tff(c_230, plain, (![A_106, B_107]: (r2_hidden(A_106, k3_tarski(B_107)) | ~r2_hidden(k1_tarski(A_106), B_107))), inference(resolution, [status(thm)], [c_58, c_188])).
% 9.16/3.31  tff(c_234, plain, (![A_106, B_78]: (r2_hidden(A_106, k3_tarski(k2_tarski(k1_tarski(A_106), B_78))))), inference(resolution, [status(thm)], [c_91, c_230])).
% 9.16/3.31  tff(c_272, plain, (![A_111, B_112]: (r2_hidden(A_111, k2_xboole_0(k1_tarski(A_111), B_112)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_234])).
% 9.16/3.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.16/3.31  tff(c_6340, plain, (![A_13754, B_13755, B_13756]: (r2_hidden(A_13754, B_13755) | ~r1_tarski(k2_xboole_0(k1_tarski(A_13754), B_13756), B_13755))), inference(resolution, [status(thm)], [c_272, c_2])).
% 9.16/3.31  tff(c_6365, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_6340])).
% 9.16/3.31  tff(c_6377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_6365])).
% 9.16/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.16/3.31  
% 9.16/3.31  Inference rules
% 9.16/3.31  ----------------------
% 9.16/3.31  #Ref     : 0
% 9.16/3.31  #Sup     : 684
% 9.16/3.31  #Fact    : 18
% 9.16/3.31  #Define  : 0
% 9.16/3.31  #Split   : 1
% 9.16/3.31  #Chain   : 0
% 9.16/3.31  #Close   : 0
% 9.16/3.31  
% 9.16/3.31  Ordering : KBO
% 9.16/3.31  
% 9.16/3.31  Simplification rules
% 9.16/3.31  ----------------------
% 9.16/3.31  #Subsume      : 89
% 9.16/3.31  #Demod        : 161
% 9.16/3.31  #Tautology    : 186
% 9.16/3.31  #SimpNegUnit  : 1
% 9.16/3.31  #BackRed      : 0
% 9.16/3.32  
% 9.16/3.32  #Partial instantiations: 4140
% 9.16/3.32  #Strategies tried      : 1
% 9.16/3.32  
% 9.16/3.32  Timing (in seconds)
% 9.16/3.32  ----------------------
% 9.16/3.32  Preprocessing        : 0.54
% 9.16/3.32  Parsing              : 0.26
% 9.16/3.32  CNF conversion       : 0.04
% 9.16/3.32  Main loop            : 1.91
% 9.16/3.32  Inferencing          : 1.02
% 9.16/3.32  Reduction            : 0.49
% 9.16/3.32  Demodulation         : 0.38
% 9.16/3.32  BG Simplification    : 0.08
% 9.16/3.32  Subsumption          : 0.23
% 9.16/3.32  Abstraction          : 0.08
% 9.16/3.32  MUC search           : 0.00
% 9.16/3.32  Cooper               : 0.00
% 9.16/3.32  Total                : 2.49
% 9.16/3.32  Index Insertion      : 0.00
% 9.16/3.32  Index Deletion       : 0.00
% 9.16/3.32  Index Matching       : 0.00
% 9.16/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
