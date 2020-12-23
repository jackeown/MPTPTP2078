%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   41 (  44 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   38 (  42 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_17] :
      ( r2_xboole_0(k1_xboole_0,A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_589,plain,(
    ! [A_69,B_70,A_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_xboole_0(A_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_608,plain,(
    ! [A_74,B_75] :
      ( ~ r1_xboole_0(A_74,B_75)
      | k3_xboole_0(A_74,B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_589])).

tff(c_617,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_608])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_630,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_14])).

tff(c_641,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_630])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_749,plain,(
    ! [C_78] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_78)) = k4_xboole_0('#skF_3',C_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_12])).

tff(c_765,plain,(
    ! [C_78] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_78)) = k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_16])).

tff(c_777,plain,(
    ! [C_78] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_78)) = k3_xboole_0('#skF_3',C_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_765])).

tff(c_20,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.41  
% 2.66/1.42  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.66/1.42  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.66/1.42  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.66/1.42  tff(f_62, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.66/1.42  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.66/1.42  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.66/1.42  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.66/1.42  tff(f_53, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.66/1.42  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.42  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.42  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.42  tff(c_18, plain, (![A_17]: (r2_xboole_0(k1_xboole_0, A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.42  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.42  tff(c_40, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.42  tff(c_589, plain, (![A_69, B_70, A_71]: (~r1_xboole_0(A_69, B_70) | ~r2_xboole_0(A_71, k3_xboole_0(A_69, B_70)))), inference(resolution, [status(thm)], [c_8, c_40])).
% 2.66/1.42  tff(c_608, plain, (![A_74, B_75]: (~r1_xboole_0(A_74, B_75) | k3_xboole_0(A_74, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_589])).
% 2.66/1.42  tff(c_617, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_608])).
% 2.66/1.42  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.42  tff(c_630, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_617, c_14])).
% 2.66/1.42  tff(c_641, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_630])).
% 2.66/1.42  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.42  tff(c_749, plain, (![C_78]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_78))=k4_xboole_0('#skF_3', C_78))), inference(superposition, [status(thm), theory('equality')], [c_641, c_12])).
% 2.66/1.42  tff(c_765, plain, (![C_78]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_78))=k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_78)))), inference(superposition, [status(thm), theory('equality')], [c_749, c_16])).
% 2.66/1.42  tff(c_777, plain, (![C_78]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_78))=k3_xboole_0('#skF_3', C_78))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_765])).
% 2.66/1.42  tff(c_20, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.42  tff(c_1195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_777, c_20])).
% 2.66/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  Inference rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Ref     : 0
% 2.66/1.42  #Sup     : 285
% 2.66/1.42  #Fact    : 0
% 2.66/1.42  #Define  : 0
% 2.66/1.42  #Split   : 1
% 2.66/1.42  #Chain   : 0
% 2.66/1.42  #Close   : 0
% 2.66/1.42  
% 2.66/1.42  Ordering : KBO
% 2.66/1.42  
% 2.66/1.42  Simplification rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Subsume      : 6
% 2.66/1.42  #Demod        : 192
% 2.66/1.42  #Tautology    : 140
% 2.66/1.42  #SimpNegUnit  : 5
% 2.66/1.42  #BackRed      : 2
% 2.66/1.42  
% 2.66/1.42  #Partial instantiations: 0
% 2.66/1.42  #Strategies tried      : 1
% 2.66/1.42  
% 2.66/1.42  Timing (in seconds)
% 2.66/1.42  ----------------------
% 2.66/1.42  Preprocessing        : 0.27
% 2.66/1.42  Parsing              : 0.15
% 2.66/1.42  CNF conversion       : 0.02
% 2.66/1.42  Main loop            : 0.38
% 2.66/1.42  Inferencing          : 0.15
% 2.66/1.42  Reduction            : 0.13
% 2.66/1.42  Demodulation         : 0.10
% 2.66/1.42  BG Simplification    : 0.02
% 2.66/1.42  Subsumption          : 0.05
% 2.66/1.42  Abstraction          : 0.02
% 2.66/1.42  MUC search           : 0.00
% 2.66/1.42  Cooper               : 0.00
% 2.66/1.42  Total                : 0.67
% 2.66/1.42  Index Insertion      : 0.00
% 2.66/1.42  Index Deletion       : 0.00
% 2.66/1.42  Index Matching       : 0.00
% 2.66/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
