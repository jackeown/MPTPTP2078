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
% DateTime   : Thu Dec  3 09:42:50 EST 2020

% Result     : Theorem 1.35s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_10])).

tff(c_17,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:41:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.35/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/1.03  
% 1.35/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/1.03  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.35/1.03  
% 1.35/1.03  %Foreground sorts:
% 1.35/1.03  
% 1.35/1.03  
% 1.35/1.03  %Background operators:
% 1.35/1.03  
% 1.35/1.03  
% 1.35/1.03  %Foreground operators:
% 1.35/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.35/1.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.35/1.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.35/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.35/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.35/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.35/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.35/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.35/1.03  
% 1.52/1.04  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.52/1.04  tff(f_36, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.52/1.04  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.52/1.04  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.04  tff(c_6, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.04  tff(c_9, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.52/1.04  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.04  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.52/1.04  tff(c_13, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_10])).
% 1.52/1.04  tff(c_17, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9, c_13])).
% 1.52/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.04  
% 1.52/1.04  Inference rules
% 1.52/1.04  ----------------------
% 1.52/1.04  #Ref     : 0
% 1.52/1.04  #Sup     : 1
% 1.52/1.04  #Fact    : 0
% 1.52/1.04  #Define  : 0
% 1.52/1.04  #Split   : 0
% 1.52/1.04  #Chain   : 0
% 1.52/1.04  #Close   : 0
% 1.52/1.04  
% 1.52/1.04  Ordering : KBO
% 1.52/1.04  
% 1.52/1.04  Simplification rules
% 1.52/1.04  ----------------------
% 1.52/1.04  #Subsume      : 0
% 1.52/1.04  #Demod        : 1
% 1.52/1.04  #Tautology    : 0
% 1.52/1.04  #SimpNegUnit  : 1
% 1.52/1.04  #BackRed      : 0
% 1.52/1.04  
% 1.52/1.04  #Partial instantiations: 0
% 1.52/1.04  #Strategies tried      : 1
% 1.52/1.04  
% 1.52/1.04  Timing (in seconds)
% 1.52/1.04  ----------------------
% 1.52/1.04  Preprocessing        : 0.24
% 1.52/1.04  Parsing              : 0.13
% 1.52/1.04  CNF conversion       : 0.01
% 1.52/1.04  Main loop            : 0.06
% 1.52/1.04  Inferencing          : 0.03
% 1.52/1.04  Reduction            : 0.02
% 1.52/1.04  Demodulation         : 0.01
% 1.52/1.04  BG Simplification    : 0.01
% 1.52/1.04  Subsumption          : 0.00
% 1.52/1.04  Abstraction          : 0.00
% 1.52/1.04  MUC search           : 0.00
% 1.52/1.04  Cooper               : 0.00
% 1.52/1.04  Total                : 0.32
% 1.52/1.04  Index Insertion      : 0.00
% 1.52/1.04  Index Deletion       : 0.00
% 1.52/1.04  Index Matching       : 0.00
% 1.52/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
