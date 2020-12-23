%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_14])).

tff(c_28,plain,(
    ! [B_12,A_13,C_14] :
      ( r1_xboole_0(B_12,k4_xboole_0(A_13,C_14))
      | ~ r1_xboole_0(A_13,k4_xboole_0(B_12,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_13] :
      ( r1_xboole_0('#skF_1',k4_xboole_0(A_13,'#skF_2'))
      | ~ r1_xboole_0(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_32,plain,(
    ! [A_13] : r1_xboole_0('#skF_1',k4_xboole_0(A_13,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_10,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.08  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.08  
% 1.64/1.08  %Foreground sorts:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Background operators:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Foreground operators:
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.08  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.08  
% 1.64/1.09  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.64/1.09  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.64/1.09  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.64/1.09  tff(f_35, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.64/1.09  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.09  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.09  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.09  tff(c_18, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_14])).
% 1.64/1.09  tff(c_28, plain, (![B_12, A_13, C_14]: (r1_xboole_0(B_12, k4_xboole_0(A_13, C_14)) | ~r1_xboole_0(A_13, k4_xboole_0(B_12, C_14)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.09  tff(c_30, plain, (![A_13]: (r1_xboole_0('#skF_1', k4_xboole_0(A_13, '#skF_2')) | ~r1_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_28])).
% 1.64/1.09  tff(c_32, plain, (![A_13]: (r1_xboole_0('#skF_1', k4_xboole_0(A_13, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 1.64/1.09  tff(c_10, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.09  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 1.64/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  Inference rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Ref     : 0
% 1.64/1.09  #Sup     : 5
% 1.64/1.09  #Fact    : 0
% 1.64/1.09  #Define  : 0
% 1.64/1.09  #Split   : 0
% 1.64/1.09  #Chain   : 0
% 1.64/1.09  #Close   : 0
% 1.64/1.09  
% 1.64/1.09  Ordering : KBO
% 1.64/1.09  
% 1.64/1.09  Simplification rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Subsume      : 0
% 1.64/1.09  #Demod        : 2
% 1.64/1.09  #Tautology    : 3
% 1.64/1.09  #SimpNegUnit  : 0
% 1.64/1.09  #BackRed      : 1
% 1.64/1.09  
% 1.64/1.09  #Partial instantiations: 0
% 1.64/1.09  #Strategies tried      : 1
% 1.64/1.09  
% 1.64/1.09  Timing (in seconds)
% 1.64/1.09  ----------------------
% 1.64/1.10  Preprocessing        : 0.25
% 1.64/1.10  Parsing              : 0.14
% 1.64/1.10  CNF conversion       : 0.01
% 1.64/1.10  Main loop            : 0.08
% 1.64/1.10  Inferencing          : 0.04
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.02
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.01
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.36
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
