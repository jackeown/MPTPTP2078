%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:21 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  51 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k1_tarski(A_9),k2_tarski(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_29,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_106,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(k1_tarski(A_11),k1_tarski(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_106,c_16])).

tff(c_78,plain,(
    ! [A_26,A_27,B_28] :
      ( r1_tarski(A_26,k2_tarski(A_27,B_28))
      | ~ r1_tarski(A_26,k1_tarski(A_27)) ) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_18,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(B_21,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_63,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_57])).

tff(c_90,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_63])).

tff(c_121,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_90])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.23  %$ r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.90/1.23  
% 1.90/1.23  %Foreground sorts:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Background operators:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Foreground operators:
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.23  
% 1.90/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.90/1.24  tff(f_43, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.90/1.24  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.90/1.24  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.90/1.24  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.90/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.24  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.24  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.24  tff(c_68, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.90/1.24  tff(c_92, plain, (![A_29]: (r1_tarski(A_29, k1_tarski('#skF_3')) | ~r1_tarski(A_29, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.90/1.24  tff(c_106, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_92])).
% 1.90/1.24  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(k1_tarski(A_11), k1_tarski(B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.24  tff(c_118, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_106, c_16])).
% 1.90/1.24  tff(c_78, plain, (![A_26, A_27, B_28]: (r1_tarski(A_26, k2_tarski(A_27, B_28)) | ~r1_tarski(A_26, k1_tarski(A_27)))), inference(resolution, [status(thm)], [c_14, c_68])).
% 1.90/1.24  tff(c_18, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.24  tff(c_53, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.24  tff(c_57, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | ~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_53])).
% 1.90/1.24  tff(c_63, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_57])).
% 1.90/1.24  tff(c_90, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_63])).
% 1.90/1.24  tff(c_121, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_90])).
% 1.90/1.24  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_121])).
% 1.90/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.24  
% 1.90/1.24  Inference rules
% 1.90/1.24  ----------------------
% 1.90/1.24  #Ref     : 0
% 1.90/1.24  #Sup     : 22
% 1.90/1.24  #Fact    : 0
% 1.90/1.24  #Define  : 0
% 1.90/1.24  #Split   : 0
% 1.90/1.24  #Chain   : 0
% 1.90/1.24  #Close   : 0
% 1.90/1.24  
% 1.90/1.24  Ordering : KBO
% 1.90/1.24  
% 1.90/1.24  Simplification rules
% 1.90/1.24  ----------------------
% 1.90/1.24  #Subsume      : 1
% 1.90/1.24  #Demod        : 12
% 1.90/1.24  #Tautology    : 12
% 1.90/1.24  #SimpNegUnit  : 1
% 1.90/1.24  #BackRed      : 6
% 1.90/1.24  
% 1.90/1.24  #Partial instantiations: 0
% 1.90/1.24  #Strategies tried      : 1
% 1.90/1.24  
% 1.90/1.24  Timing (in seconds)
% 1.90/1.24  ----------------------
% 1.90/1.25  Preprocessing        : 0.31
% 1.90/1.25  Parsing              : 0.16
% 1.90/1.25  CNF conversion       : 0.02
% 1.90/1.25  Main loop            : 0.12
% 1.90/1.25  Inferencing          : 0.04
% 1.90/1.25  Reduction            : 0.04
% 1.90/1.25  Demodulation         : 0.03
% 1.90/1.25  BG Simplification    : 0.01
% 1.90/1.25  Subsumption          : 0.02
% 1.90/1.25  Abstraction          : 0.01
% 1.90/1.25  MUC search           : 0.00
% 1.90/1.25  Cooper               : 0.00
% 1.90/1.25  Total                : 0.45
% 1.90/1.25  Index Insertion      : 0.00
% 1.90/1.25  Index Deletion       : 0.00
% 1.90/1.25  Index Matching       : 0.00
% 1.90/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
