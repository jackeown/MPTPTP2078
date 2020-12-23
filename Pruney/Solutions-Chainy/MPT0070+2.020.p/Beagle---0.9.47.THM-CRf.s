%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  57 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_81,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_26])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_86])).

tff(c_112,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_112])).

tff(c_127,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_121])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_36,B_37] : k2_xboole_0(k3_xboole_0(A_36,B_37),k4_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_7,k1_xboole_0)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_191,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_183])).

tff(c_436,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,C_47)) = k4_xboole_0(A_45,k4_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_469,plain,(
    ! [C_47] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_47)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_436])).

tff(c_904,plain,(
    ! [C_57] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_57)) = k3_xboole_0('#skF_1',C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_469])).

tff(c_948,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_904])).

tff(c_965,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_948])).

tff(c_967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:23:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.51  
% 2.92/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.51  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.92/1.51  
% 2.92/1.51  %Foreground sorts:
% 2.92/1.51  
% 2.92/1.51  
% 2.92/1.51  %Background operators:
% 2.92/1.51  
% 2.92/1.51  
% 2.92/1.51  %Foreground operators:
% 2.92/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.51  
% 2.92/1.52  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.92/1.52  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.92/1.52  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.92/1.52  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.92/1.52  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.92/1.52  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.92/1.52  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.92/1.52  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.92/1.52  tff(c_81, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.52  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.52  tff(c_85, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_26])).
% 2.92/1.52  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.52  tff(c_99, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.52  tff(c_107, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_99])).
% 2.92/1.52  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.52  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.52  tff(c_86, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.52  tff(c_94, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_86])).
% 2.92/1.52  tff(c_112, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.52  tff(c_121, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_94, c_112])).
% 2.92/1.52  tff(c_127, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_121])).
% 2.92/1.52  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.52  tff(c_162, plain, (![A_36, B_37]: (k2_xboole_0(k3_xboole_0(A_36, B_37), k4_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.52  tff(c_183, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_7, k1_xboole_0))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_12, c_162])).
% 2.92/1.52  tff(c_191, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_183])).
% 2.92/1.52  tff(c_436, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, C_47))=k4_xboole_0(A_45, k4_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.52  tff(c_469, plain, (![C_47]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_47))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_47)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_436])).
% 2.92/1.52  tff(c_904, plain, (![C_57]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_57))=k3_xboole_0('#skF_1', C_57))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_469])).
% 2.92/1.52  tff(c_948, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_904])).
% 2.92/1.52  tff(c_965, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_948])).
% 2.92/1.52  tff(c_967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_965])).
% 2.92/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.52  
% 2.92/1.52  Inference rules
% 2.92/1.52  ----------------------
% 2.92/1.52  #Ref     : 0
% 2.92/1.52  #Sup     : 228
% 2.92/1.52  #Fact    : 0
% 2.92/1.52  #Define  : 0
% 2.92/1.52  #Split   : 0
% 2.92/1.52  #Chain   : 0
% 2.92/1.52  #Close   : 0
% 2.92/1.52  
% 2.92/1.52  Ordering : KBO
% 2.92/1.52  
% 2.92/1.52  Simplification rules
% 2.92/1.52  ----------------------
% 2.92/1.52  #Subsume      : 0
% 2.92/1.52  #Demod        : 191
% 2.92/1.52  #Tautology    : 158
% 2.92/1.52  #SimpNegUnit  : 1
% 2.92/1.52  #BackRed      : 2
% 2.92/1.52  
% 2.92/1.52  #Partial instantiations: 0
% 2.92/1.52  #Strategies tried      : 1
% 2.92/1.52  
% 2.92/1.52  Timing (in seconds)
% 2.92/1.52  ----------------------
% 2.92/1.52  Preprocessing        : 0.36
% 2.92/1.52  Parsing              : 0.22
% 2.92/1.52  CNF conversion       : 0.02
% 2.92/1.52  Main loop            : 0.40
% 2.92/1.52  Inferencing          : 0.14
% 2.92/1.52  Reduction            : 0.16
% 2.92/1.52  Demodulation         : 0.13
% 2.92/1.52  BG Simplification    : 0.02
% 2.92/1.52  Subsumption          : 0.06
% 2.92/1.52  Abstraction          : 0.02
% 2.92/1.52  MUC search           : 0.00
% 2.92/1.52  Cooper               : 0.00
% 2.92/1.52  Total                : 0.79
% 2.92/1.52  Index Insertion      : 0.00
% 2.92/1.52  Index Deletion       : 0.00
% 2.92/1.52  Index Matching       : 0.00
% 2.92/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
