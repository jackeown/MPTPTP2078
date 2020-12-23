%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_xboole_0(A_6,C_8),B_7)
      | ~ r1_tarski(C_8,B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),k3_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_17,B_18,B_19] :
      ( r1_tarski(k5_xboole_0(A_17,B_18),B_19)
      | ~ r1_tarski(k2_xboole_0(A_17,B_18),B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4])).

tff(c_8,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_27,c_8])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.11  
% 1.57/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.11  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.57/1.11  
% 1.57/1.11  %Foreground sorts:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Background operators:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Foreground operators:
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.57/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.57/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.57/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.57/1.11  
% 1.57/1.12  tff(f_44, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 1.57/1.12  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.57/1.12  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 1.57/1.12  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.57/1.12  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.12  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.12  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_xboole_0(A_6, C_8), B_7) | ~r1_tarski(C_8, B_7) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.57/1.12  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), k3_xboole_0(A_12, B_13))=k5_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.12  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.12  tff(c_27, plain, (![A_17, B_18, B_19]: (r1_tarski(k5_xboole_0(A_17, B_18), B_19) | ~r1_tarski(k2_xboole_0(A_17, B_18), B_19))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4])).
% 1.57/1.12  tff(c_8, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.12  tff(c_31, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_27, c_8])).
% 1.57/1.12  tff(c_34, plain, (~r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_31])).
% 1.57/1.12  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_34])).
% 1.57/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.12  
% 1.57/1.12  Inference rules
% 1.57/1.12  ----------------------
% 1.57/1.12  #Ref     : 0
% 1.57/1.12  #Sup     : 5
% 1.57/1.12  #Fact    : 0
% 1.57/1.12  #Define  : 0
% 1.57/1.12  #Split   : 0
% 1.57/1.12  #Chain   : 0
% 1.57/1.12  #Close   : 0
% 1.57/1.12  
% 1.57/1.12  Ordering : KBO
% 1.57/1.12  
% 1.57/1.12  Simplification rules
% 1.57/1.12  ----------------------
% 1.57/1.12  #Subsume      : 0
% 1.57/1.12  #Demod        : 2
% 1.57/1.12  #Tautology    : 2
% 1.57/1.12  #SimpNegUnit  : 0
% 1.57/1.12  #BackRed      : 0
% 1.57/1.12  
% 1.57/1.12  #Partial instantiations: 0
% 1.57/1.12  #Strategies tried      : 1
% 1.57/1.12  
% 1.57/1.12  Timing (in seconds)
% 1.57/1.12  ----------------------
% 1.57/1.12  Preprocessing        : 0.24
% 1.57/1.12  Parsing              : 0.14
% 1.57/1.12  CNF conversion       : 0.01
% 1.57/1.12  Main loop            : 0.08
% 1.57/1.12  Inferencing          : 0.04
% 1.57/1.12  Reduction            : 0.02
% 1.57/1.12  Demodulation         : 0.02
% 1.57/1.12  BG Simplification    : 0.01
% 1.57/1.12  Subsumption          : 0.01
% 1.57/1.12  Abstraction          : 0.00
% 1.57/1.12  MUC search           : 0.00
% 1.57/1.12  Cooper               : 0.00
% 1.57/1.12  Total                : 0.34
% 1.57/1.12  Index Insertion      : 0.00
% 1.57/1.12  Index Deletion       : 0.00
% 1.57/1.12  Index Matching       : 0.00
% 1.57/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
