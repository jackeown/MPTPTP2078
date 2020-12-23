%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:49 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k2_xboole_0(B,C))
       => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_10,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_191,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(k4_xboole_0(A_37,C_38),k4_xboole_0(B_39,C_38))
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_494,plain,(
    ! [A_71,B_72,A_73] :
      ( r1_tarski(k4_xboole_0(A_71,B_72),k4_xboole_0(A_73,B_72))
      | ~ r1_tarski(A_71,k2_xboole_0(A_73,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(B_21,C_20)
      | ~ r1_tarski(A_19,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_19,A_9,B_10] :
      ( r1_tarski(A_19,A_9)
      | ~ r1_tarski(A_19,k4_xboole_0(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_527,plain,(
    ! [A_74,B_75,A_76] :
      ( r1_tarski(k4_xboole_0(A_74,B_75),A_76)
      | ~ r1_tarski(A_74,k2_xboole_0(A_76,B_75)) ) ),
    inference(resolution,[status(thm)],[c_494,c_73])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_546,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_527,c_12])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.30  
% 2.53/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.53/1.31  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.53/1.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.53/1.31  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.53/1.31  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.53/1.31  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.53/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.31  tff(c_14, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.31  tff(c_15, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.53/1.31  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.31  tff(c_191, plain, (![A_37, C_38, B_39]: (r1_tarski(k4_xboole_0(A_37, C_38), k4_xboole_0(B_39, C_38)) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.31  tff(c_494, plain, (![A_71, B_72, A_73]: (r1_tarski(k4_xboole_0(A_71, B_72), k4_xboole_0(A_73, B_72)) | ~r1_tarski(A_71, k2_xboole_0(A_73, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_191])).
% 2.53/1.31  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.31  tff(c_68, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, C_20) | ~r1_tarski(B_21, C_20) | ~r1_tarski(A_19, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.31  tff(c_73, plain, (![A_19, A_9, B_10]: (r1_tarski(A_19, A_9) | ~r1_tarski(A_19, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_8, c_68])).
% 2.53/1.31  tff(c_527, plain, (![A_74, B_75, A_76]: (r1_tarski(k4_xboole_0(A_74, B_75), A_76) | ~r1_tarski(A_74, k2_xboole_0(A_76, B_75)))), inference(resolution, [status(thm)], [c_494, c_73])).
% 2.53/1.31  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.31  tff(c_546, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_527, c_12])).
% 2.53/1.31  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15, c_546])).
% 2.53/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  Inference rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Ref     : 0
% 2.53/1.31  #Sup     : 140
% 2.53/1.31  #Fact    : 0
% 2.53/1.31  #Define  : 0
% 2.53/1.31  #Split   : 0
% 2.53/1.31  #Chain   : 0
% 2.53/1.31  #Close   : 0
% 2.53/1.31  
% 2.53/1.31  Ordering : KBO
% 2.53/1.31  
% 2.53/1.31  Simplification rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Subsume      : 4
% 2.53/1.31  #Demod        : 36
% 2.53/1.31  #Tautology    : 34
% 2.53/1.31  #SimpNegUnit  : 0
% 2.53/1.31  #BackRed      : 0
% 2.53/1.31  
% 2.53/1.31  #Partial instantiations: 0
% 2.53/1.31  #Strategies tried      : 1
% 2.53/1.31  
% 2.53/1.31  Timing (in seconds)
% 2.53/1.31  ----------------------
% 2.53/1.31  Preprocessing        : 0.25
% 2.53/1.31  Parsing              : 0.14
% 2.53/1.31  CNF conversion       : 0.01
% 2.53/1.31  Main loop            : 0.31
% 2.53/1.31  Inferencing          : 0.10
% 2.53/1.31  Reduction            : 0.11
% 2.53/1.31  Demodulation         : 0.09
% 2.53/1.31  BG Simplification    : 0.01
% 2.53/1.31  Subsumption          : 0.06
% 2.53/1.31  Abstraction          : 0.01
% 2.53/1.31  MUC search           : 0.00
% 2.53/1.31  Cooper               : 0.00
% 2.53/1.31  Total                : 0.58
% 2.53/1.31  Index Insertion      : 0.00
% 2.53/1.31  Index Deletion       : 0.00
% 2.53/1.31  Index Matching       : 0.00
% 2.53/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
