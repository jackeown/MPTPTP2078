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
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_677,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_62,B_63),k3_xboole_0(A_62,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_8])).

tff(c_713,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_677])).

tff(c_736,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_713])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_280,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(A_39,C_40)
      | ~ r1_tarski(k2_tarski(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_285,plain,(
    ! [A_39,B_4,B_41] :
      ( r2_hidden(A_39,B_4)
      | k4_xboole_0(k2_tarski(A_39,B_41),B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_280])).

tff(c_750,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_285])).

tff(c_779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.47  
% 2.49/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.47  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.47  
% 2.49/1.47  %Foreground sorts:
% 2.49/1.47  
% 2.49/1.47  
% 2.49/1.47  %Background operators:
% 2.49/1.47  
% 2.49/1.47  
% 2.49/1.47  %Foreground operators:
% 2.49/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.47  
% 2.49/1.48  tff(f_48, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 2.49/1.48  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.49/1.48  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.49/1.48  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.49/1.48  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.49/1.48  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.49/1.48  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.48  tff(c_20, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.48  tff(c_152, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.48  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.48  tff(c_677, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_62, B_63), k3_xboole_0(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_8])).
% 2.49/1.48  tff(c_713, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_677])).
% 2.49/1.48  tff(c_736, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_713])).
% 2.49/1.48  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.48  tff(c_280, plain, (![A_39, C_40, B_41]: (r2_hidden(A_39, C_40) | ~r1_tarski(k2_tarski(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.48  tff(c_285, plain, (![A_39, B_4, B_41]: (r2_hidden(A_39, B_4) | k4_xboole_0(k2_tarski(A_39, B_41), B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_280])).
% 2.49/1.48  tff(c_750, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_736, c_285])).
% 2.49/1.48  tff(c_779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_750])).
% 2.49/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.48  
% 2.49/1.48  Inference rules
% 2.49/1.48  ----------------------
% 2.49/1.48  #Ref     : 0
% 2.49/1.48  #Sup     : 190
% 2.49/1.48  #Fact    : 0
% 2.49/1.48  #Define  : 0
% 2.49/1.48  #Split   : 0
% 2.49/1.48  #Chain   : 0
% 2.49/1.48  #Close   : 0
% 2.49/1.48  
% 2.49/1.48  Ordering : KBO
% 2.49/1.48  
% 2.49/1.48  Simplification rules
% 2.49/1.48  ----------------------
% 2.49/1.48  #Subsume      : 10
% 2.49/1.48  #Demod        : 131
% 2.49/1.48  #Tautology    : 115
% 2.49/1.48  #SimpNegUnit  : 1
% 2.49/1.48  #BackRed      : 1
% 2.49/1.48  
% 2.49/1.48  #Partial instantiations: 0
% 2.49/1.48  #Strategies tried      : 1
% 2.49/1.48  
% 2.49/1.48  Timing (in seconds)
% 2.49/1.48  ----------------------
% 2.49/1.48  Preprocessing        : 0.36
% 2.49/1.48  Parsing              : 0.21
% 2.49/1.48  CNF conversion       : 0.02
% 2.49/1.48  Main loop            : 0.31
% 2.49/1.48  Inferencing          : 0.13
% 2.49/1.48  Reduction            : 0.10
% 2.49/1.48  Demodulation         : 0.08
% 2.49/1.48  BG Simplification    : 0.01
% 2.49/1.48  Subsumption          : 0.05
% 2.49/1.48  Abstraction          : 0.02
% 2.49/1.48  MUC search           : 0.00
% 2.49/1.48  Cooper               : 0.00
% 2.49/1.48  Total                : 0.70
% 2.49/1.48  Index Insertion      : 0.00
% 2.49/1.48  Index Deletion       : 0.00
% 2.49/1.48  Index Matching       : 0.00
% 2.60/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
