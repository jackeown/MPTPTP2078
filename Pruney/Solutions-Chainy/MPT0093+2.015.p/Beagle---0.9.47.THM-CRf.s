%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:33 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  25 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),k4_xboole_0(B_2,C_3))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_1',k4_xboole_0(B_13,'#skF_3'))
      | ~ r1_tarski('#skF_1',B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2])).

tff(c_8,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_8])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.13  
% 1.56/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.14  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.56/1.14  
% 1.56/1.14  %Foreground sorts:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Background operators:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Foreground operators:
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.56/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.14  
% 1.56/1.14  tff(f_40, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.56/1.14  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.56/1.14  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 1.56/1.14  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.14  tff(c_10, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.14  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.14  tff(c_22, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_10, c_14])).
% 1.56/1.14  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), k4_xboole_0(B_2, C_3)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.14  tff(c_34, plain, (![B_13]: (r1_tarski('#skF_1', k4_xboole_0(B_13, '#skF_3')) | ~r1_tarski('#skF_1', B_13))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2])).
% 1.56/1.14  tff(c_8, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.14  tff(c_37, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_8])).
% 1.56/1.14  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_37])).
% 1.56/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  Inference rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Ref     : 0
% 1.56/1.14  #Sup     : 8
% 1.56/1.14  #Fact    : 0
% 1.56/1.14  #Define  : 0
% 1.56/1.14  #Split   : 0
% 1.56/1.14  #Chain   : 0
% 1.56/1.14  #Close   : 0
% 1.56/1.14  
% 1.56/1.14  Ordering : KBO
% 1.56/1.14  
% 1.56/1.14  Simplification rules
% 1.56/1.14  ----------------------
% 1.56/1.14  #Subsume      : 0
% 1.56/1.14  #Demod        : 1
% 1.56/1.14  #Tautology    : 3
% 1.56/1.14  #SimpNegUnit  : 0
% 1.56/1.14  #BackRed      : 0
% 1.56/1.14  
% 1.56/1.14  #Partial instantiations: 0
% 1.56/1.14  #Strategies tried      : 1
% 1.56/1.14  
% 1.56/1.14  Timing (in seconds)
% 1.56/1.14  ----------------------
% 1.56/1.15  Preprocessing        : 0.26
% 1.56/1.15  Parsing              : 0.15
% 1.56/1.15  CNF conversion       : 0.01
% 1.56/1.15  Main loop            : 0.08
% 1.56/1.15  Inferencing          : 0.04
% 1.56/1.15  Reduction            : 0.02
% 1.56/1.15  Demodulation         : 0.02
% 1.56/1.15  BG Simplification    : 0.01
% 1.56/1.15  Subsumption          : 0.01
% 1.56/1.15  Abstraction          : 0.00
% 1.56/1.15  MUC search           : 0.00
% 1.56/1.15  Cooper               : 0.00
% 1.56/1.15  Total                : 0.37
% 1.56/1.15  Index Insertion      : 0.00
% 1.56/1.15  Index Deletion       : 0.00
% 1.56/1.15  Index Matching       : 0.00
% 1.56/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
