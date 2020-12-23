%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    5 (   5 expanded)
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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_30])).

tff(c_46,plain,(
    ! [B_17,A_18,C_19] :
      ( r1_xboole_0(B_17,k4_xboole_0(A_18,C_19))
      | ~ r1_xboole_0(A_18,k4_xboole_0(B_17,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_18] :
      ( r1_xboole_0('#skF_1',k4_xboole_0(A_18,'#skF_2'))
      | ~ r1_xboole_0(A_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_55,plain,(
    ! [A_18] : r1_xboole_0('#skF_1',k4_xboole_0(A_18,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_48])).

tff(c_12,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n001.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 20:54:30 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.43/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.03  
% 1.43/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/1.03  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.43/1.03  
% 1.43/1.03  %Foreground sorts:
% 1.43/1.03  
% 1.43/1.03  
% 1.43/1.03  %Background operators:
% 1.43/1.03  
% 1.43/1.03  
% 1.43/1.03  %Foreground operators:
% 1.43/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.43/1.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.43/1.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.43/1.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.43/1.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.43/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.43/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.43/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.43/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.43/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.43/1.03  
% 1.55/1.04  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.55/1.04  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.55/1.04  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.55/1.04  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.55/1.04  tff(f_37, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.55/1.04  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.04  tff(c_24, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.04  tff(c_27, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_24])).
% 1.55/1.04  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.55/1.04  tff(c_30, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.04  tff(c_38, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_30])).
% 1.55/1.04  tff(c_46, plain, (![B_17, A_18, C_19]: (r1_xboole_0(B_17, k4_xboole_0(A_18, C_19)) | ~r1_xboole_0(A_18, k4_xboole_0(B_17, C_19)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.55/1.04  tff(c_48, plain, (![A_18]: (r1_xboole_0('#skF_1', k4_xboole_0(A_18, '#skF_2')) | ~r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_46])).
% 1.55/1.04  tff(c_55, plain, (![A_18]: (r1_xboole_0('#skF_1', k4_xboole_0(A_18, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_48])).
% 1.55/1.04  tff(c_12, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.55/1.04  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_12])).
% 1.55/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.04  
% 1.55/1.04  Inference rules
% 1.55/1.04  ----------------------
% 1.55/1.04  #Ref     : 0
% 1.55/1.04  #Sup     : 11
% 1.55/1.04  #Fact    : 0
% 1.55/1.04  #Define  : 0
% 1.55/1.04  #Split   : 0
% 1.55/1.04  #Chain   : 0
% 1.55/1.04  #Close   : 0
% 1.55/1.04  
% 1.55/1.04  Ordering : KBO
% 1.55/1.04  
% 1.55/1.04  Simplification rules
% 1.55/1.04  ----------------------
% 1.55/1.04  #Subsume      : 0
% 1.55/1.04  #Demod        : 3
% 1.55/1.04  #Tautology    : 5
% 1.55/1.04  #SimpNegUnit  : 0
% 1.55/1.04  #BackRed      : 1
% 1.55/1.04  
% 1.55/1.04  #Partial instantiations: 0
% 1.55/1.04  #Strategies tried      : 1
% 1.55/1.04  
% 1.55/1.04  Timing (in seconds)
% 1.55/1.04  ----------------------
% 1.55/1.05  Preprocessing        : 0.24
% 1.55/1.05  Parsing              : 0.14
% 1.55/1.05  CNF conversion       : 0.01
% 1.55/1.05  Main loop            : 0.09
% 1.55/1.05  Inferencing          : 0.04
% 1.55/1.05  Reduction            : 0.03
% 1.55/1.05  Demodulation         : 0.02
% 1.55/1.05  BG Simplification    : 0.01
% 1.55/1.05  Subsumption          : 0.02
% 1.55/1.05  Abstraction          : 0.00
% 1.55/1.05  MUC search           : 0.00
% 1.55/1.05  Cooper               : 0.00
% 1.55/1.05  Total                : 0.36
% 1.55/1.05  Index Insertion      : 0.00
% 1.55/1.05  Index Deletion       : 0.00
% 1.55/1.05  Index Matching       : 0.00
% 1.55/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
