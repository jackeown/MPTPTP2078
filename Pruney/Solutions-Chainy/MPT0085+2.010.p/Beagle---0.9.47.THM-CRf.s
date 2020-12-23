%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_49,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_14])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_24] :
      ( r2_xboole_0(k1_xboole_0,A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_495,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_671,plain,(
    ! [A_72,B_73,A_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_xboole_0(A_74,k3_xboole_0(A_72,B_73)) ) ),
    inference(resolution,[status(thm)],[c_10,c_495])).

tff(c_688,plain,(
    ! [A_79,B_80] :
      ( ~ r1_xboole_0(A_79,B_80)
      | k3_xboole_0(A_79,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_671])).

tff(c_692,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_688])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k3_xboole_0(A_14,B_15),k3_xboole_0(A_14,C_16)) = k3_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_702,plain,(
    ! [C_16] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_16)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_16])).

tff(c_723,plain,(
    ! [C_16] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_16)) = k3_xboole_0('#skF_3',C_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_702])).

tff(c_28,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n010.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 18:19:59 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.26  
% 2.46/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.27  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.46/1.27  
% 2.46/1.27  %Foreground sorts:
% 2.46/1.27  
% 2.46/1.27  
% 2.46/1.27  %Background operators:
% 2.46/1.27  
% 2.46/1.27  
% 2.46/1.27  %Foreground operators:
% 2.46/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.46/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.46/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.46/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.27  
% 2.46/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.46/1.28  tff(f_57, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.46/1.28  tff(f_77, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.46/1.28  tff(f_72, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.46/1.28  tff(f_51, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.46/1.28  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.46/1.28  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.46/1.28  tff(c_49, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.28  tff(c_14, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.28  tff(c_65, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_49, c_14])).
% 2.46/1.28  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.28  tff(c_26, plain, (![A_24]: (r2_xboole_0(k1_xboole_0, A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.28  tff(c_10, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.28  tff(c_495, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.28  tff(c_671, plain, (![A_72, B_73, A_74]: (~r1_xboole_0(A_72, B_73) | ~r2_xboole_0(A_74, k3_xboole_0(A_72, B_73)))), inference(resolution, [status(thm)], [c_10, c_495])).
% 2.46/1.28  tff(c_688, plain, (![A_79, B_80]: (~r1_xboole_0(A_79, B_80) | k3_xboole_0(A_79, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_671])).
% 2.46/1.28  tff(c_692, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_688])).
% 2.46/1.28  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k3_xboole_0(A_14, C_16))=k3_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.28  tff(c_702, plain, (![C_16]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_16))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_16)))), inference(superposition, [status(thm), theory('equality')], [c_692, c_16])).
% 2.46/1.28  tff(c_723, plain, (![C_16]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_16))=k3_xboole_0('#skF_3', C_16))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_702])).
% 2.46/1.28  tff(c_28, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.28  tff(c_964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_723, c_28])).
% 2.46/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.28  
% 2.46/1.28  Inference rules
% 2.46/1.28  ----------------------
% 2.46/1.28  #Ref     : 0
% 2.46/1.28  #Sup     : 221
% 2.46/1.28  #Fact    : 0
% 2.46/1.28  #Define  : 0
% 2.46/1.28  #Split   : 1
% 2.46/1.28  #Chain   : 0
% 2.46/1.28  #Close   : 0
% 2.46/1.28  
% 2.46/1.28  Ordering : KBO
% 2.46/1.28  
% 2.46/1.28  Simplification rules
% 2.46/1.28  ----------------------
% 2.46/1.28  #Subsume      : 7
% 2.46/1.28  #Demod        : 151
% 2.46/1.28  #Tautology    : 170
% 2.46/1.28  #SimpNegUnit  : 2
% 2.46/1.28  #BackRed      : 2
% 2.46/1.28  
% 2.46/1.28  #Partial instantiations: 0
% 2.46/1.28  #Strategies tried      : 1
% 2.46/1.28  
% 2.46/1.28  Timing (in seconds)
% 2.46/1.28  ----------------------
% 2.46/1.28  Preprocessing        : 0.29
% 2.46/1.28  Parsing              : 0.16
% 2.46/1.28  CNF conversion       : 0.02
% 2.46/1.28  Main loop            : 0.33
% 2.46/1.28  Inferencing          : 0.12
% 2.46/1.28  Reduction            : 0.13
% 2.46/1.28  Demodulation         : 0.10
% 2.46/1.28  BG Simplification    : 0.02
% 2.46/1.28  Subsumption          : 0.05
% 2.46/1.28  Abstraction          : 0.01
% 2.46/1.28  MUC search           : 0.00
% 2.46/1.28  Cooper               : 0.00
% 2.46/1.28  Total                : 0.65
% 2.46/1.28  Index Insertion      : 0.00
% 2.46/1.28  Index Deletion       : 0.00
% 2.46/1.28  Index Matching       : 0.00
% 2.46/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
