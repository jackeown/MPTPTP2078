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
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_266,plain,(
    ! [A_48,B_49] : r1_tarski(k4_xboole_0(A_48,B_49),k5_xboole_0(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_278,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),k5_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_266])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_zfmisc_1(A_25),k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),k5_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1051,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(k2_xboole_0(A_81,C_82),B_83)
      | ~ r1_tarski(C_82,B_83)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1078,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1051,c_30])).

tff(c_1129,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1078])).

tff(c_1486,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_1129])).

tff(c_1490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1486])).

tff(c_1491,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_1849,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_1491])).

tff(c_1853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.16/1.49  
% 3.16/1.49  %Foreground sorts:
% 3.16/1.49  
% 3.16/1.49  
% 3.16/1.49  %Background operators:
% 3.16/1.49  
% 3.16/1.49  
% 3.16/1.49  %Foreground operators:
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.49  
% 3.16/1.49  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.16/1.49  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 3.16/1.49  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.16/1.49  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.16/1.49  tff(f_66, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 3.16/1.49  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.49  tff(c_266, plain, (![A_48, B_49]: (r1_tarski(k4_xboole_0(A_48, B_49), k5_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.49  tff(c_278, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), k5_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_266])).
% 3.16/1.49  tff(c_26, plain, (![A_25, B_26]: (r1_tarski(k1_zfmisc_1(A_25), k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.49  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), k5_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.49  tff(c_1051, plain, (![A_81, C_82, B_83]: (r1_tarski(k2_xboole_0(A_81, C_82), B_83) | ~r1_tarski(C_82, B_83) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.49  tff(c_30, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.49  tff(c_1078, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1051, c_30])).
% 3.16/1.49  tff(c_1129, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1078])).
% 3.16/1.49  tff(c_1486, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1129])).
% 3.16/1.49  tff(c_1490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1486])).
% 3.16/1.49  tff(c_1491, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1078])).
% 3.16/1.49  tff(c_1849, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1491])).
% 3.16/1.49  tff(c_1853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_1849])).
% 3.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  Inference rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Ref     : 0
% 3.16/1.49  #Sup     : 451
% 3.16/1.49  #Fact    : 0
% 3.16/1.49  #Define  : 0
% 3.16/1.49  #Split   : 1
% 3.16/1.49  #Chain   : 0
% 3.16/1.49  #Close   : 0
% 3.16/1.49  
% 3.16/1.49  Ordering : KBO
% 3.16/1.49  
% 3.16/1.49  Simplification rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Subsume      : 9
% 3.16/1.49  #Demod        : 248
% 3.16/1.49  #Tautology    : 289
% 3.16/1.49  #SimpNegUnit  : 0
% 3.16/1.50  #BackRed      : 2
% 3.16/1.50  
% 3.16/1.50  #Partial instantiations: 0
% 3.16/1.50  #Strategies tried      : 1
% 3.16/1.50  
% 3.16/1.50  Timing (in seconds)
% 3.16/1.50  ----------------------
% 3.16/1.50  Preprocessing        : 0.29
% 3.16/1.50  Parsing              : 0.17
% 3.16/1.50  CNF conversion       : 0.02
% 3.16/1.50  Main loop            : 0.45
% 3.16/1.50  Inferencing          : 0.15
% 3.16/1.50  Reduction            : 0.19
% 3.16/1.50  Demodulation         : 0.16
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.06
% 3.16/1.50  Abstraction          : 0.02
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.77
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
