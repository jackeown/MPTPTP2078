%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_8,C_30] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_78,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_75])).

tff(c_18,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,(
    ! [A_32,B_33] :
      ( ~ r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_103,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_727,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_800,plain,(
    ! [C_60] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_60)) = k4_xboole_0(k1_xboole_0,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_727])).

tff(c_826,plain,(
    ! [C_61] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_61)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_800])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_837,plain,(
    ! [C_61] :
      ( r2_hidden('#skF_1'('#skF_3',k4_xboole_0('#skF_4',C_61)),k1_xboole_0)
      | r1_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_2])).

tff(c_876,plain,(
    ! [C_61] : r1_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_61)) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_837])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.42  
% 2.34/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.42  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.34/1.42  
% 2.34/1.42  %Foreground sorts:
% 2.34/1.42  
% 2.34/1.42  
% 2.34/1.42  %Background operators:
% 2.34/1.42  
% 2.34/1.42  
% 2.34/1.42  %Foreground operators:
% 2.34/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.42  
% 2.60/1.43  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.60/1.43  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.60/1.43  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.43  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.43  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.60/1.43  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.60/1.43  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.60/1.43  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.60/1.43  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.43  tff(c_58, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.43  tff(c_61, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.60/1.43  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.43  tff(c_68, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.43  tff(c_75, plain, (![A_8, C_30]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.60/1.43  tff(c_78, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_75])).
% 2.60/1.43  tff(c_18, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.60/1.43  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.43  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.43  tff(c_86, plain, (![A_32, B_33]: (~r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.60/1.43  tff(c_103, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_86])).
% 2.60/1.43  tff(c_727, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.43  tff(c_800, plain, (![C_60]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_60))=k4_xboole_0(k1_xboole_0, C_60))), inference(superposition, [status(thm), theory('equality')], [c_103, c_727])).
% 2.60/1.43  tff(c_826, plain, (![C_61]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_61))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_800])).
% 2.60/1.43  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.43  tff(c_837, plain, (![C_61]: (r2_hidden('#skF_1'('#skF_3', k4_xboole_0('#skF_4', C_61)), k1_xboole_0) | r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_61)))), inference(superposition, [status(thm), theory('equality')], [c_826, c_2])).
% 2.60/1.43  tff(c_876, plain, (![C_61]: (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_61)))), inference(negUnitSimplification, [status(thm)], [c_78, c_837])).
% 2.60/1.43  tff(c_22, plain, (~r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.43  tff(c_888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_876, c_22])).
% 2.60/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.43  
% 2.60/1.43  Inference rules
% 2.60/1.43  ----------------------
% 2.60/1.43  #Ref     : 0
% 2.60/1.43  #Sup     : 211
% 2.60/1.43  #Fact    : 0
% 2.60/1.43  #Define  : 0
% 2.60/1.43  #Split   : 0
% 2.60/1.43  #Chain   : 0
% 2.60/1.43  #Close   : 0
% 2.60/1.43  
% 2.60/1.43  Ordering : KBO
% 2.60/1.43  
% 2.60/1.43  Simplification rules
% 2.60/1.43  ----------------------
% 2.60/1.43  #Subsume      : 8
% 2.60/1.43  #Demod        : 170
% 2.60/1.43  #Tautology    : 149
% 2.60/1.43  #SimpNegUnit  : 7
% 2.60/1.43  #BackRed      : 1
% 2.60/1.43  
% 2.60/1.43  #Partial instantiations: 0
% 2.60/1.43  #Strategies tried      : 1
% 2.60/1.43  
% 2.60/1.43  Timing (in seconds)
% 2.60/1.43  ----------------------
% 2.60/1.43  Preprocessing        : 0.29
% 2.60/1.43  Parsing              : 0.16
% 2.60/1.43  CNF conversion       : 0.02
% 2.60/1.43  Main loop            : 0.28
% 2.60/1.43  Inferencing          : 0.11
% 2.60/1.43  Reduction            : 0.10
% 2.60/1.43  Demodulation         : 0.08
% 2.60/1.43  BG Simplification    : 0.01
% 2.60/1.43  Subsumption          : 0.04
% 2.60/1.43  Abstraction          : 0.02
% 2.60/1.43  MUC search           : 0.00
% 2.60/1.43  Cooper               : 0.00
% 2.60/1.43  Total                : 0.59
% 2.60/1.43  Index Insertion      : 0.00
% 2.60/1.43  Index Deletion       : 0.00
% 2.60/1.43  Index Matching       : 0.00
% 2.60/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
