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
% DateTime   : Thu Dec  3 09:51:55 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   47 (  49 expanded)
%              Number of leaves         :   31 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_153,plain,(
    ! [A_8,C_64] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_155,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_153])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_119,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_xboole_0) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_125,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_80])).

tff(c_24,plain,(
    ! [D_23,B_19] : r2_hidden(D_23,k2_tarski(D_23,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_146,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_24])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:56:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.21  
% 1.98/1.22  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.98/1.22  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.98/1.22  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.22  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.98/1.22  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.98/1.22  tff(f_78, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.98/1.22  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.98/1.22  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.98/1.22  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.22  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.22  tff(c_150, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.22  tff(c_153, plain, (![A_8, C_64]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_150])).
% 1.98/1.22  tff(c_155, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_153])).
% 1.98/1.22  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.22  tff(c_106, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.22  tff(c_115, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 1.98/1.22  tff(c_119, plain, (![A_61]: (k4_xboole_0(A_61, k1_xboole_0)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_115])).
% 1.98/1.22  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.98/1.22  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.22  tff(c_80, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_10])).
% 1.98/1.22  tff(c_125, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_119, c_80])).
% 1.98/1.22  tff(c_24, plain, (![D_23, B_19]: (r2_hidden(D_23, k2_tarski(D_23, B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_146, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_24])).
% 1.98/1.22  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_146])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 28
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 0
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 0
% 1.98/1.22  #Demod        : 5
% 1.98/1.22  #Tautology    : 21
% 1.98/1.22  #SimpNegUnit  : 2
% 1.98/1.22  #BackRed      : 4
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 2.07/1.22  Preprocessing        : 0.34
% 2.07/1.22  Parsing              : 0.18
% 2.07/1.22  CNF conversion       : 0.02
% 2.07/1.22  Main loop            : 0.13
% 2.07/1.22  Inferencing          : 0.04
% 2.07/1.22  Reduction            : 0.05
% 2.07/1.22  Demodulation         : 0.04
% 2.07/1.22  BG Simplification    : 0.01
% 2.07/1.22  Subsumption          : 0.02
% 2.07/1.22  Abstraction          : 0.01
% 2.07/1.22  MUC search           : 0.00
% 2.07/1.22  Cooper               : 0.00
% 2.07/1.22  Total                : 0.49
% 2.07/1.22  Index Insertion      : 0.00
% 2.07/1.22  Index Deletion       : 0.00
% 2.07/1.22  Index Matching       : 0.00
% 2.07/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
