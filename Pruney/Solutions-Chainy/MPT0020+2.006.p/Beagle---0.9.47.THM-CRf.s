%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_47,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,C_19)
      | ~ r1_tarski(k2_xboole_0(A_18,B_20),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [C_21] :
      ( r1_tarski('#skF_1',C_21)
      | ~ r1_tarski('#skF_2',C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_47])).

tff(c_64,plain,(
    ! [B_10] : r1_tarski('#skF_1',k2_xboole_0('#skF_2',B_10)) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_356,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k2_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(C_47,B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_373,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_356,c_12])).

tff(c_400,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_373])).

tff(c_404,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_400])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.25  
% 2.07/1.25  %Foreground sorts:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Background operators:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Foreground operators:
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.25  
% 2.07/1.26  tff(f_52, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 2.07/1.26  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.07/1.26  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.26  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.07/1.26  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.07/1.26  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.26  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.26  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.26  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.26  tff(c_30, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.07/1.26  tff(c_47, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, C_19) | ~r1_tarski(k2_xboole_0(A_18, B_20), C_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.26  tff(c_59, plain, (![C_21]: (r1_tarski('#skF_1', C_21) | ~r1_tarski('#skF_2', C_21))), inference(superposition, [status(thm), theory('equality')], [c_30, c_47])).
% 2.07/1.26  tff(c_64, plain, (![B_10]: (r1_tarski('#skF_1', k2_xboole_0('#skF_2', B_10)))), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.07/1.26  tff(c_356, plain, (![A_46, C_47, B_48]: (r1_tarski(k2_xboole_0(A_46, C_47), B_48) | ~r1_tarski(C_47, B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.26  tff(c_12, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.26  tff(c_373, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_4')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_356, c_12])).
% 2.07/1.26  tff(c_400, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_373])).
% 2.07/1.26  tff(c_404, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2, c_400])).
% 2.07/1.26  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_404])).
% 2.07/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  Inference rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Ref     : 0
% 2.07/1.26  #Sup     : 92
% 2.07/1.26  #Fact    : 0
% 2.07/1.26  #Define  : 0
% 2.07/1.26  #Split   : 0
% 2.07/1.26  #Chain   : 0
% 2.07/1.26  #Close   : 0
% 2.07/1.26  
% 2.07/1.26  Ordering : KBO
% 2.07/1.26  
% 2.07/1.26  Simplification rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Subsume      : 8
% 2.07/1.26  #Demod        : 40
% 2.07/1.26  #Tautology    : 49
% 2.07/1.26  #SimpNegUnit  : 0
% 2.07/1.26  #BackRed      : 0
% 2.07/1.26  
% 2.07/1.26  #Partial instantiations: 0
% 2.07/1.26  #Strategies tried      : 1
% 2.07/1.26  
% 2.07/1.26  Timing (in seconds)
% 2.07/1.26  ----------------------
% 2.07/1.26  Preprocessing        : 0.25
% 2.07/1.26  Parsing              : 0.14
% 2.07/1.26  CNF conversion       : 0.02
% 2.07/1.26  Main loop            : 0.23
% 2.07/1.26  Inferencing          : 0.10
% 2.07/1.26  Reduction            : 0.07
% 2.07/1.26  Demodulation         : 0.05
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.04
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.51
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
