%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:28 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  48 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_28,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    k4_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_14])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_15])).

tff(c_58,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [C_16] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_16)) = k4_xboole_0('#skF_1',C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [C_17] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_17)) = k4_xboole_0('#skF_1',C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_58])).

tff(c_100,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k4_xboole_0(B_2,'#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_105,plain,(
    ! [B_18] : k4_xboole_0('#skF_1',k4_xboole_0(B_18,'#skF_3')) = k4_xboole_0('#skF_1',B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_100])).

tff(c_10,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_117,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:35:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  %$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.74/1.17  
% 1.74/1.17  %Foreground sorts:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Background operators:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Foreground operators:
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.74/1.17  
% 1.74/1.17  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.74/1.17  tff(f_42, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 1.74/1.17  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.74/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.74/1.17  tff(c_28, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.17  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.17  tff(c_36, plain, (k4_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(resolution, [status(thm)], [c_28, c_14])).
% 1.74/1.17  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.17  tff(c_15, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.17  tff(c_23, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_15])).
% 1.74/1.17  tff(c_58, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.17  tff(c_79, plain, (![C_16]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_16))=k4_xboole_0('#skF_1', C_16))), inference(superposition, [status(thm), theory('equality')], [c_23, c_58])).
% 1.74/1.17  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.17  tff(c_84, plain, (![C_17]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_17))=k4_xboole_0('#skF_1', C_17))), inference(superposition, [status(thm), theory('equality')], [c_23, c_58])).
% 1.74/1.17  tff(c_100, plain, (![B_2]: (k4_xboole_0('#skF_1', k4_xboole_0(B_2, '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 1.74/1.17  tff(c_105, plain, (![B_18]: (k4_xboole_0('#skF_1', k4_xboole_0(B_18, '#skF_3'))=k4_xboole_0('#skF_1', B_18))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_100])).
% 1.74/1.17  tff(c_10, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.17  tff(c_22, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.74/1.17  tff(c_117, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 1.74/1.17  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_117])).
% 1.74/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  Inference rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Ref     : 0
% 1.74/1.17  #Sup     : 32
% 1.74/1.17  #Fact    : 0
% 1.74/1.17  #Define  : 0
% 1.74/1.17  #Split   : 0
% 1.74/1.17  #Chain   : 0
% 1.74/1.17  #Close   : 0
% 1.74/1.17  
% 1.74/1.17  Ordering : KBO
% 1.74/1.17  
% 1.74/1.17  Simplification rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Subsume      : 0
% 1.74/1.17  #Demod        : 7
% 1.74/1.17  #Tautology    : 14
% 1.74/1.17  #SimpNegUnit  : 1
% 1.74/1.17  #BackRed      : 0
% 1.74/1.17  
% 1.74/1.17  #Partial instantiations: 0
% 1.74/1.17  #Strategies tried      : 1
% 1.74/1.17  
% 1.74/1.17  Timing (in seconds)
% 1.74/1.17  ----------------------
% 1.74/1.18  Preprocessing        : 0.23
% 1.74/1.18  Parsing              : 0.13
% 1.74/1.18  CNF conversion       : 0.01
% 1.74/1.18  Main loop            : 0.12
% 1.74/1.18  Inferencing          : 0.05
% 1.74/1.18  Reduction            : 0.04
% 1.74/1.18  Demodulation         : 0.03
% 1.74/1.18  BG Simplification    : 0.01
% 1.74/1.18  Subsumption          : 0.02
% 1.74/1.18  Abstraction          : 0.01
% 1.74/1.18  MUC search           : 0.00
% 1.74/1.18  Cooper               : 0.00
% 1.74/1.18  Total                : 0.38
% 1.74/1.18  Index Insertion      : 0.00
% 1.74/1.18  Index Deletion       : 0.00
% 1.74/1.18  Index Matching       : 0.00
% 1.74/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
