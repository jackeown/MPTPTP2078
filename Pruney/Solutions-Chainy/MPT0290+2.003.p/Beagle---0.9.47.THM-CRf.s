%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_12,plain,(
    ! [B_12,A_13] : k3_xboole_0(B_12,A_13) = k3_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [B_12,A_13] : r1_tarski(k3_xboole_0(B_12,A_13),A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k3_tarski(A_8),k3_tarski(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k3_xboole_0(B_19,C_20))
      | ~ r1_tarski(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_10])).

tff(c_73,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_76,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_81,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_85,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.13  %$ r1_tarski > k3_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.13  
% 1.63/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.14  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.63/1.14  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.63/1.14  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.63/1.14  tff(f_42, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 1.63/1.14  tff(c_12, plain, (![B_12, A_13]: (k3_xboole_0(B_12, A_13)=k3_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.14  tff(c_27, plain, (![B_12, A_13]: (r1_tarski(k3_xboole_0(B_12, A_13), A_13))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4])).
% 1.63/1.14  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_tarski(A_8), k3_tarski(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.14  tff(c_62, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k3_xboole_0(B_19, C_20)) | ~r1_tarski(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.14  tff(c_10, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.14  tff(c_72, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_10])).
% 1.63/1.14  tff(c_73, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_72])).
% 1.63/1.14  tff(c_76, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8, c_73])).
% 1.63/1.14  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_76])).
% 1.63/1.14  tff(c_81, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_72])).
% 1.63/1.14  tff(c_85, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_8, c_81])).
% 1.63/1.14  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_85])).
% 1.63/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  Inference rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Ref     : 0
% 1.63/1.14  #Sup     : 17
% 1.63/1.14  #Fact    : 0
% 1.63/1.14  #Define  : 0
% 1.63/1.14  #Split   : 1
% 1.63/1.14  #Chain   : 0
% 1.63/1.14  #Close   : 0
% 1.63/1.14  
% 1.63/1.14  Ordering : KBO
% 1.63/1.14  
% 1.63/1.14  Simplification rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Subsume      : 2
% 1.63/1.14  #Demod        : 5
% 1.63/1.14  #Tautology    : 11
% 1.63/1.14  #SimpNegUnit  : 0
% 1.63/1.14  #BackRed      : 0
% 1.63/1.14  
% 1.63/1.14  #Partial instantiations: 0
% 1.63/1.14  #Strategies tried      : 1
% 1.63/1.14  
% 1.63/1.14  Timing (in seconds)
% 1.63/1.14  ----------------------
% 1.63/1.14  Preprocessing        : 0.26
% 1.63/1.14  Parsing              : 0.14
% 1.63/1.14  CNF conversion       : 0.01
% 1.63/1.14  Main loop            : 0.12
% 1.63/1.14  Inferencing          : 0.04
% 1.63/1.14  Reduction            : 0.04
% 1.63/1.14  Demodulation         : 0.04
% 1.63/1.14  BG Simplification    : 0.01
% 1.63/1.14  Subsumption          : 0.02
% 1.63/1.14  Abstraction          : 0.00
% 1.63/1.14  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.40
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
