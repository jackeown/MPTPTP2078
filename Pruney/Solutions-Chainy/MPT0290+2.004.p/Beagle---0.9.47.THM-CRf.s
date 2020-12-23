%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   31 (  42 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_69,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k3_tarski(A_10),k3_tarski(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_105,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,k3_xboole_0(B_27,C_28))
      | ~ r1_tarski(A_26,C_28)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_250,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_253,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_253])).

tff(c_258,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_262,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_258])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:47:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1
% 2.02/1.25  
% 2.02/1.25  %Foreground sorts:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Background operators:
% 2.02/1.25  
% 2.02/1.25  
% 2.02/1.25  %Foreground operators:
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.25  
% 2.02/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.02/1.26  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.26  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.02/1.26  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.02/1.26  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.02/1.26  tff(f_44, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 2.02/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.26  tff(c_48, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.26  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.26  tff(c_66, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6])).
% 2.02/1.26  tff(c_69, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.02/1.26  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k3_tarski(A_10), k3_tarski(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.26  tff(c_57, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6])).
% 2.02/1.26  tff(c_105, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, k3_xboole_0(B_27, C_28)) | ~r1_tarski(A_26, C_28) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.26  tff(c_12, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.26  tff(c_115, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_12])).
% 2.02/1.26  tff(c_250, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_115])).
% 2.02/1.26  tff(c_253, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_10, c_250])).
% 2.02/1.26  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_253])).
% 2.02/1.26  tff(c_258, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_115])).
% 2.02/1.26  tff(c_262, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_258])).
% 2.02/1.26  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_262])).
% 2.02/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  Inference rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Ref     : 0
% 2.02/1.26  #Sup     : 62
% 2.02/1.26  #Fact    : 0
% 2.02/1.26  #Define  : 0
% 2.02/1.26  #Split   : 1
% 2.02/1.26  #Chain   : 0
% 2.02/1.26  #Close   : 0
% 2.02/1.26  
% 2.02/1.26  Ordering : KBO
% 2.02/1.26  
% 2.02/1.26  Simplification rules
% 2.02/1.26  ----------------------
% 2.02/1.26  #Subsume      : 2
% 2.02/1.26  #Demod        : 23
% 2.02/1.26  #Tautology    : 33
% 2.02/1.26  #SimpNegUnit  : 0
% 2.02/1.26  #BackRed      : 0
% 2.02/1.26  
% 2.02/1.26  #Partial instantiations: 0
% 2.02/1.26  #Strategies tried      : 1
% 2.02/1.26  
% 2.02/1.26  Timing (in seconds)
% 2.02/1.26  ----------------------
% 2.02/1.26  Preprocessing        : 0.27
% 2.02/1.26  Parsing              : 0.15
% 2.02/1.26  CNF conversion       : 0.01
% 2.02/1.26  Main loop            : 0.21
% 2.02/1.26  Inferencing          : 0.07
% 2.02/1.26  Reduction            : 0.09
% 2.02/1.26  Demodulation         : 0.08
% 2.02/1.26  BG Simplification    : 0.01
% 2.02/1.26  Subsumption          : 0.03
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.50
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
