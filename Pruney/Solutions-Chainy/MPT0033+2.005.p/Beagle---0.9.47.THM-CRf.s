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
% DateTime   : Thu Dec  3 09:42:37 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  35 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_15,plain,(
    ! [B_13,A_14] : k3_xboole_0(B_13,A_14) = k3_xboole_0(A_14,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [B_13,A_14] : r1_tarski(k3_xboole_0(B_13,A_14),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_4])).

tff(c_222,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k3_xboole_0(B_39,C_40))
      | ~ r1_tarski(A_38,C_40)
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_13,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_232,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_222,c_13])).

tff(c_244,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_232])).

tff(c_247,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_244])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.94/1.21  
% 1.94/1.21  %Foreground sorts:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Background operators:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Foreground operators:
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.21  
% 2.05/1.22  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.05/1.22  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 2.05/1.22  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.05/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.22  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.05/1.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.22  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_64, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.22  tff(c_73, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_64])).
% 2.05/1.22  tff(c_15, plain, (![B_13, A_14]: (k3_xboole_0(B_13, A_14)=k3_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.22  tff(c_30, plain, (![B_13, A_14]: (r1_tarski(k3_xboole_0(B_13, A_14), A_14))), inference(superposition, [status(thm), theory('equality')], [c_15, c_4])).
% 2.05/1.22  tff(c_222, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k3_xboole_0(B_39, C_40)) | ~r1_tarski(A_38, C_40) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.22  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_13, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 2.05/1.22  tff(c_232, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_222, c_13])).
% 2.05/1.22  tff(c_244, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_232])).
% 2.05/1.22  tff(c_247, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_73, c_244])).
% 2.05/1.22  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_247])).
% 2.05/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  Inference rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Ref     : 0
% 2.05/1.22  #Sup     : 59
% 2.05/1.22  #Fact    : 0
% 2.05/1.22  #Define  : 0
% 2.05/1.22  #Split   : 0
% 2.05/1.22  #Chain   : 0
% 2.05/1.22  #Close   : 0
% 2.05/1.22  
% 2.05/1.22  Ordering : KBO
% 2.05/1.22  
% 2.05/1.22  Simplification rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Subsume      : 3
% 2.05/1.22  #Demod        : 16
% 2.05/1.22  #Tautology    : 22
% 2.05/1.22  #SimpNegUnit  : 0
% 2.05/1.22  #BackRed      : 0
% 2.05/1.22  
% 2.05/1.22  #Partial instantiations: 0
% 2.05/1.22  #Strategies tried      : 1
% 2.05/1.22  
% 2.05/1.22  Timing (in seconds)
% 2.05/1.22  ----------------------
% 2.05/1.23  Preprocessing        : 0.26
% 2.05/1.23  Parsing              : 0.15
% 2.05/1.23  CNF conversion       : 0.02
% 2.05/1.23  Main loop            : 0.20
% 2.05/1.23  Inferencing          : 0.06
% 2.05/1.23  Reduction            : 0.08
% 2.05/1.23  Demodulation         : 0.07
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.04
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.49
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
