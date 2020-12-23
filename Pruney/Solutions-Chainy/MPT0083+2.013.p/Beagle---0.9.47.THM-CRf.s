%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [B_16,A_17] : r1_tarski(k3_xboole_0(B_16,A_17),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_6])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_xboole_0(A_32,C_33)
      | ~ r1_xboole_0(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [A_35] :
      ( r1_xboole_0(A_35,'#skF_2')
      | ~ r1_tarski(A_35,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_192])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [A_37] :
      ( r1_xboole_0('#skF_2',A_37)
      | ~ r1_tarski(A_37,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_199,c_4])).

tff(c_12,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_755,plain,(
    ! [A_75,A_76] :
      ( r1_xboole_0(A_75,A_76)
      | ~ r1_tarski(A_75,'#skF_2')
      | ~ r1_tarski(A_76,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_213,c_12])).

tff(c_893,plain,(
    ! [A_83,A_84] :
      ( r1_xboole_0(A_83,A_84)
      | ~ r1_tarski(A_84,'#skF_2')
      | ~ r1_tarski(A_83,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_755,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_898,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_893,c_17])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34,c_898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.75/1.44  
% 2.75/1.44  %Foreground sorts:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Background operators:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Foreground operators:
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.44  
% 2.75/1.45  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.75/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.75/1.45  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.75/1.45  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.75/1.45  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.75/1.45  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.45  tff(c_19, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.45  tff(c_34, plain, (![B_16, A_17]: (r1_tarski(k3_xboole_0(B_16, A_17), A_17))), inference(superposition, [status(thm), theory('equality')], [c_19, c_6])).
% 2.75/1.45  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.45  tff(c_192, plain, (![A_32, C_33, B_34]: (r1_xboole_0(A_32, C_33) | ~r1_xboole_0(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.45  tff(c_199, plain, (![A_35]: (r1_xboole_0(A_35, '#skF_2') | ~r1_tarski(A_35, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_192])).
% 2.75/1.45  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.45  tff(c_213, plain, (![A_37]: (r1_xboole_0('#skF_2', A_37) | ~r1_tarski(A_37, '#skF_1'))), inference(resolution, [status(thm)], [c_199, c_4])).
% 2.75/1.45  tff(c_12, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.45  tff(c_755, plain, (![A_75, A_76]: (r1_xboole_0(A_75, A_76) | ~r1_tarski(A_75, '#skF_2') | ~r1_tarski(A_76, '#skF_1'))), inference(resolution, [status(thm)], [c_213, c_12])).
% 2.75/1.45  tff(c_893, plain, (![A_83, A_84]: (r1_xboole_0(A_83, A_84) | ~r1_tarski(A_84, '#skF_2') | ~r1_tarski(A_83, '#skF_1'))), inference(resolution, [status(thm)], [c_755, c_4])).
% 2.75/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.45  tff(c_14, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.45  tff(c_17, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.75/1.45  tff(c_898, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_893, c_17])).
% 2.75/1.45  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_34, c_898])).
% 2.75/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  Inference rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Ref     : 0
% 2.75/1.45  #Sup     : 242
% 2.75/1.45  #Fact    : 0
% 2.75/1.45  #Define  : 0
% 2.75/1.45  #Split   : 1
% 2.75/1.45  #Chain   : 0
% 2.75/1.45  #Close   : 0
% 2.75/1.45  
% 2.75/1.45  Ordering : KBO
% 2.75/1.45  
% 2.75/1.45  Simplification rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Subsume      : 70
% 2.75/1.45  #Demod        : 167
% 2.75/1.45  #Tautology    : 103
% 2.75/1.45  #SimpNegUnit  : 0
% 2.75/1.45  #BackRed      : 0
% 2.75/1.45  
% 2.75/1.45  #Partial instantiations: 0
% 2.75/1.45  #Strategies tried      : 1
% 2.75/1.45  
% 2.75/1.45  Timing (in seconds)
% 2.75/1.45  ----------------------
% 2.75/1.45  Preprocessing        : 0.27
% 2.75/1.45  Parsing              : 0.15
% 2.75/1.45  CNF conversion       : 0.01
% 2.75/1.45  Main loop            : 0.38
% 2.75/1.45  Inferencing          : 0.12
% 2.75/1.45  Reduction            : 0.15
% 2.75/1.45  Demodulation         : 0.12
% 2.75/1.45  BG Simplification    : 0.01
% 2.75/1.45  Subsumption          : 0.07
% 2.75/1.45  Abstraction          : 0.02
% 2.75/1.45  MUC search           : 0.00
% 2.75/1.45  Cooper               : 0.00
% 2.75/1.45  Total                : 0.67
% 2.75/1.45  Index Insertion      : 0.00
% 2.75/1.45  Index Deletion       : 0.00
% 2.75/1.45  Index Matching       : 0.00
% 2.75/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
