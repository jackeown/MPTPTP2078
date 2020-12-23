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
% DateTime   : Thu Dec  3 09:44:33 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  48 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_71,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k4_xboole_0(A_20,B_21),C_22) = k4_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,(
    ! [C_22] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_22)) = k4_xboole_0('#skF_1',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_71])).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [C_23] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_23)) = k4_xboole_0('#skF_1',C_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_71])).

tff(c_113,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',k4_xboole_0(B_4,'#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_117,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',k4_xboole_0(B_4,'#skF_3')) = k4_xboole_0('#skF_1',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_113])).

tff(c_19,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19,c_14])).

tff(c_222,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_23])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.35  
% 2.01/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.35  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.35  
% 2.01/1.35  %Foreground sorts:
% 2.01/1.35  
% 2.01/1.35  
% 2.01/1.35  %Background operators:
% 2.01/1.35  
% 2.01/1.35  
% 2.01/1.35  %Foreground operators:
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.35  
% 2.01/1.36  tff(f_44, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.01/1.36  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.01/1.36  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.01/1.36  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.01/1.36  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.01/1.36  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.36  tff(c_24, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.36  tff(c_32, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_24])).
% 2.01/1.36  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.36  tff(c_37, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.36  tff(c_41, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.01/1.36  tff(c_71, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k4_xboole_0(A_20, B_21), C_22)=k4_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.36  tff(c_89, plain, (![C_22]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_22))=k4_xboole_0('#skF_1', C_22))), inference(superposition, [status(thm), theory('equality')], [c_41, c_71])).
% 2.01/1.36  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.36  tff(c_97, plain, (![C_23]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_23))=k4_xboole_0('#skF_1', C_23))), inference(superposition, [status(thm), theory('equality')], [c_41, c_71])).
% 2.01/1.36  tff(c_113, plain, (![B_4]: (k4_xboole_0('#skF_1', k4_xboole_0(B_4, '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 2.01/1.36  tff(c_117, plain, (![B_4]: (k4_xboole_0('#skF_1', k4_xboole_0(B_4, '#skF_3'))=k4_xboole_0('#skF_1', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_113])).
% 2.01/1.36  tff(c_19, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.36  tff(c_14, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.36  tff(c_23, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_19, c_14])).
% 2.01/1.36  tff(c_222, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_117, c_23])).
% 2.01/1.36  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_222])).
% 2.01/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.36  
% 2.01/1.36  Inference rules
% 2.01/1.36  ----------------------
% 2.01/1.36  #Ref     : 0
% 2.01/1.36  #Sup     : 54
% 2.01/1.36  #Fact    : 0
% 2.01/1.36  #Define  : 0
% 2.01/1.36  #Split   : 0
% 2.01/1.36  #Chain   : 0
% 2.01/1.36  #Close   : 0
% 2.01/1.36  
% 2.01/1.36  Ordering : KBO
% 2.01/1.36  
% 2.01/1.36  Simplification rules
% 2.01/1.36  ----------------------
% 2.01/1.36  #Subsume      : 0
% 2.01/1.36  #Demod        : 21
% 2.01/1.36  #Tautology    : 26
% 2.01/1.36  #SimpNegUnit  : 0
% 2.01/1.36  #BackRed      : 1
% 2.01/1.36  
% 2.01/1.36  #Partial instantiations: 0
% 2.01/1.36  #Strategies tried      : 1
% 2.01/1.36  
% 2.01/1.36  Timing (in seconds)
% 2.01/1.36  ----------------------
% 2.01/1.36  Preprocessing        : 0.34
% 2.01/1.36  Parsing              : 0.19
% 2.01/1.37  CNF conversion       : 0.02
% 2.01/1.37  Main loop            : 0.19
% 2.01/1.37  Inferencing          : 0.08
% 2.01/1.37  Reduction            : 0.06
% 2.01/1.37  Demodulation         : 0.05
% 2.01/1.37  BG Simplification    : 0.01
% 2.01/1.37  Subsumption          : 0.03
% 2.01/1.37  Abstraction          : 0.01
% 2.01/1.37  MUC search           : 0.00
% 2.01/1.37  Cooper               : 0.00
% 2.01/1.37  Total                : 0.56
% 2.01/1.37  Index Insertion      : 0.00
% 2.01/1.37  Index Deletion       : 0.00
% 2.01/1.37  Index Matching       : 0.00
% 2.01/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
