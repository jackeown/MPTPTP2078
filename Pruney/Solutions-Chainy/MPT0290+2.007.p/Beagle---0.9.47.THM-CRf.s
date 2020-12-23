%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  58 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_235,plain,(
    ! [A_41,B_42,C_43] : r1_tarski(k2_xboole_0(k3_xboole_0(A_41,B_42),k3_xboole_0(A_41,C_43)),k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_271,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),k2_xboole_0(B_42,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_235])).

tff(c_281,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_271])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k3_tarski(A_13),k3_tarski(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(A_29,k3_xboole_0(B_30,C_31))
      | ~ r1_tarski(A_29,C_31)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_18])).

tff(c_722,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_725,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_722])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_725])).

tff(c_730,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_734,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_730])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_1
% 2.21/1.29  
% 2.21/1.29  %Foreground sorts:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Background operators:
% 2.21/1.29  
% 2.21/1.29  
% 2.21/1.29  %Foreground operators:
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.29  
% 2.21/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.30  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.21/1.30  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.21/1.30  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.21/1.30  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.21/1.30  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.21/1.30  tff(f_52, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 2.21/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.30  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.30  tff(c_30, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_22])).
% 2.21/1.30  tff(c_235, plain, (![A_41, B_42, C_43]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_41, B_42), k3_xboole_0(A_41, C_43)), k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.30  tff(c_271, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), k2_xboole_0(B_42, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_235])).
% 2.21/1.30  tff(c_281, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), B_42))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_271])).
% 2.21/1.30  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k3_tarski(A_13), k3_tarski(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.30  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.30  tff(c_68, plain, (![A_29, B_30, C_31]: (r1_tarski(A_29, k3_xboole_0(B_30, C_31)) | ~r1_tarski(A_29, C_31) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.30  tff(c_18, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.30  tff(c_81, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_18])).
% 2.21/1.30  tff(c_722, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_81])).
% 2.21/1.30  tff(c_725, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_16, c_722])).
% 2.21/1.30  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_725])).
% 2.21/1.30  tff(c_730, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_81])).
% 2.21/1.30  tff(c_734, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_16, c_730])).
% 2.21/1.30  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_734])).
% 2.21/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  Inference rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Ref     : 0
% 2.21/1.30  #Sup     : 169
% 2.21/1.30  #Fact    : 0
% 2.21/1.30  #Define  : 0
% 2.21/1.30  #Split   : 2
% 2.21/1.30  #Chain   : 0
% 2.21/1.30  #Close   : 0
% 2.21/1.30  
% 2.21/1.30  Ordering : KBO
% 2.21/1.30  
% 2.21/1.30  Simplification rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Subsume      : 5
% 2.21/1.30  #Demod        : 120
% 2.21/1.30  #Tautology    : 113
% 2.21/1.30  #SimpNegUnit  : 0
% 2.21/1.30  #BackRed      : 0
% 2.21/1.30  
% 2.21/1.30  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.30  Preprocessing        : 0.26
% 2.21/1.30  Parsing              : 0.15
% 2.21/1.30  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.29
% 2.21/1.30  Inferencing          : 0.11
% 2.21/1.30  Reduction            : 0.09
% 2.21/1.30  Demodulation         : 0.07
% 2.21/1.30  BG Simplification    : 0.01
% 2.21/1.30  Subsumption          : 0.05
% 2.21/1.30  Abstraction          : 0.02
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.57
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
