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
% DateTime   : Thu Dec  3 09:46:03 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   32 (  49 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 106 expanded)
%              Number of equality atoms :   40 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_56,B_57,C_58] :
      ( '#skF_3'(A_56,B_57,C_58) = B_57
      | '#skF_3'(A_56,B_57,C_58) = A_56
      | r2_hidden('#skF_4'(A_56,B_57,C_58),C_58)
      | k2_tarski(A_56,B_57) = C_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_316,plain,(
    ! [A_68,B_69,A_70] :
      ( '#skF_4'(A_68,B_69,k1_tarski(A_70)) = A_70
      | '#skF_3'(A_68,B_69,k1_tarski(A_70)) = B_69
      | '#skF_3'(A_68,B_69,k1_tarski(A_70)) = A_68
      | k2_tarski(A_68,B_69) = k1_tarski(A_70) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_26,plain,(
    ! [A_6,B_7,C_8] :
      ( '#skF_3'(A_6,B_7,C_8) = B_7
      | '#skF_3'(A_6,B_7,C_8) = A_6
      | '#skF_4'(A_6,B_7,C_8) != A_6
      | k2_tarski(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_336,plain,(
    ! [A_70,B_69] :
      ( '#skF_3'(A_70,B_69,k1_tarski(A_70)) = B_69
      | '#skF_3'(A_70,B_69,k1_tarski(A_70)) = A_70
      | k2_tarski(A_70,B_69) = k1_tarski(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_26])).

tff(c_464,plain,(
    ! [B_75] :
      ( k2_tarski(B_75,B_75) = k1_tarski(B_75)
      | '#skF_3'(B_75,B_75,k1_tarski(B_75)) = B_75 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_336])).

tff(c_113,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r2_hidden('#skF_3'(A_42,B_43,C_44),C_44)
      | r2_hidden('#skF_4'(A_42,B_43,C_44),C_44)
      | k2_tarski(A_42,B_43) = C_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_42,B_43,A_1] :
      ( '#skF_4'(A_42,B_43,k1_tarski(A_1)) = A_1
      | ~ r2_hidden('#skF_3'(A_42,B_43,k1_tarski(A_1)),k1_tarski(A_1))
      | k2_tarski(A_42,B_43) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_476,plain,(
    ! [B_75] :
      ( '#skF_4'(B_75,B_75,k1_tarski(B_75)) = B_75
      | ~ r2_hidden(B_75,k1_tarski(B_75))
      | k2_tarski(B_75,B_75) = k1_tarski(B_75)
      | k2_tarski(B_75,B_75) = k1_tarski(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_123])).

tff(c_504,plain,(
    ! [B_77] :
      ( '#skF_4'(B_77,B_77,k1_tarski(B_77)) = B_77
      | k2_tarski(B_77,B_77) = k1_tarski(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_476])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | '#skF_4'(A_6,B_7,C_8) != A_6
      | k2_tarski(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_482,plain,(
    ! [B_75] :
      ( ~ r2_hidden(B_75,k1_tarski(B_75))
      | '#skF_4'(B_75,B_75,k1_tarski(B_75)) != B_75
      | k2_tarski(B_75,B_75) = k1_tarski(B_75)
      | k2_tarski(B_75,B_75) = k1_tarski(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_24])).

tff(c_496,plain,(
    ! [B_75] :
      ( '#skF_4'(B_75,B_75,k1_tarski(B_75)) != B_75
      | k2_tarski(B_75,B_75) = k1_tarski(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_482])).

tff(c_532,plain,(
    ! [B_77] : k2_tarski(B_77,B_77) = k1_tarski(B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_496])).

tff(c_34,plain,(
    k2_tarski('#skF_5','#skF_5') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_3 > #skF_2 > #skF_1
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.15/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.29  
% 2.15/1.30  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.15/1.30  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.15/1.30  tff(f_46, negated_conjecture, ~(![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.30  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.30  tff(c_128, plain, (![A_56, B_57, C_58]: ('#skF_3'(A_56, B_57, C_58)=B_57 | '#skF_3'(A_56, B_57, C_58)=A_56 | r2_hidden('#skF_4'(A_56, B_57, C_58), C_58) | k2_tarski(A_56, B_57)=C_58)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.30  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.30  tff(c_316, plain, (![A_68, B_69, A_70]: ('#skF_4'(A_68, B_69, k1_tarski(A_70))=A_70 | '#skF_3'(A_68, B_69, k1_tarski(A_70))=B_69 | '#skF_3'(A_68, B_69, k1_tarski(A_70))=A_68 | k2_tarski(A_68, B_69)=k1_tarski(A_70))), inference(resolution, [status(thm)], [c_128, c_2])).
% 2.15/1.30  tff(c_26, plain, (![A_6, B_7, C_8]: ('#skF_3'(A_6, B_7, C_8)=B_7 | '#skF_3'(A_6, B_7, C_8)=A_6 | '#skF_4'(A_6, B_7, C_8)!=A_6 | k2_tarski(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.30  tff(c_336, plain, (![A_70, B_69]: ('#skF_3'(A_70, B_69, k1_tarski(A_70))=B_69 | '#skF_3'(A_70, B_69, k1_tarski(A_70))=A_70 | k2_tarski(A_70, B_69)=k1_tarski(A_70))), inference(superposition, [status(thm), theory('equality')], [c_316, c_26])).
% 2.15/1.30  tff(c_464, plain, (![B_75]: (k2_tarski(B_75, B_75)=k1_tarski(B_75) | '#skF_3'(B_75, B_75, k1_tarski(B_75))=B_75)), inference(factorization, [status(thm), theory('equality')], [c_336])).
% 2.15/1.30  tff(c_113, plain, (![A_42, B_43, C_44]: (~r2_hidden('#skF_3'(A_42, B_43, C_44), C_44) | r2_hidden('#skF_4'(A_42, B_43, C_44), C_44) | k2_tarski(A_42, B_43)=C_44)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.30  tff(c_123, plain, (![A_42, B_43, A_1]: ('#skF_4'(A_42, B_43, k1_tarski(A_1))=A_1 | ~r2_hidden('#skF_3'(A_42, B_43, k1_tarski(A_1)), k1_tarski(A_1)) | k2_tarski(A_42, B_43)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_113, c_2])).
% 2.15/1.30  tff(c_476, plain, (![B_75]: ('#skF_4'(B_75, B_75, k1_tarski(B_75))=B_75 | ~r2_hidden(B_75, k1_tarski(B_75)) | k2_tarski(B_75, B_75)=k1_tarski(B_75) | k2_tarski(B_75, B_75)=k1_tarski(B_75))), inference(superposition, [status(thm), theory('equality')], [c_464, c_123])).
% 2.15/1.30  tff(c_504, plain, (![B_77]: ('#skF_4'(B_77, B_77, k1_tarski(B_77))=B_77 | k2_tarski(B_77, B_77)=k1_tarski(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_476])).
% 2.15/1.30  tff(c_24, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | '#skF_4'(A_6, B_7, C_8)!=A_6 | k2_tarski(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.30  tff(c_482, plain, (![B_75]: (~r2_hidden(B_75, k1_tarski(B_75)) | '#skF_4'(B_75, B_75, k1_tarski(B_75))!=B_75 | k2_tarski(B_75, B_75)=k1_tarski(B_75) | k2_tarski(B_75, B_75)=k1_tarski(B_75))), inference(superposition, [status(thm), theory('equality')], [c_464, c_24])).
% 2.15/1.30  tff(c_496, plain, (![B_75]: ('#skF_4'(B_75, B_75, k1_tarski(B_75))!=B_75 | k2_tarski(B_75, B_75)=k1_tarski(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_482])).
% 2.15/1.30  tff(c_532, plain, (![B_77]: (k2_tarski(B_77, B_77)=k1_tarski(B_77))), inference(superposition, [status(thm), theory('equality')], [c_504, c_496])).
% 2.15/1.30  tff(c_34, plain, (k2_tarski('#skF_5', '#skF_5')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.30  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_532, c_34])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 0
% 2.15/1.30  #Sup     : 106
% 2.15/1.30  #Fact    : 4
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 0
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 35
% 2.15/1.30  #Demod        : 34
% 2.15/1.30  #Tautology    : 54
% 2.15/1.30  #SimpNegUnit  : 0
% 2.15/1.30  #BackRed      : 2
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.31  Preprocessing        : 0.28
% 2.15/1.31  Parsing              : 0.14
% 2.15/1.31  CNF conversion       : 0.02
% 2.15/1.31  Main loop            : 0.28
% 2.15/1.31  Inferencing          : 0.12
% 2.15/1.31  Reduction            : 0.07
% 2.15/1.31  Demodulation         : 0.05
% 2.15/1.31  BG Simplification    : 0.02
% 2.15/1.31  Subsumption          : 0.06
% 2.15/1.31  Abstraction          : 0.02
% 2.15/1.31  MUC search           : 0.00
% 2.15/1.31  Cooper               : 0.00
% 2.15/1.31  Total                : 0.58
% 2.15/1.31  Index Insertion      : 0.00
% 2.15/1.31  Index Deletion       : 0.00
% 2.15/1.31  Index Matching       : 0.00
% 2.15/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
