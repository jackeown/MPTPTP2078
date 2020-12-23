%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  36 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ! [C_20,A_21,B_22] :
      ( C_20 = A_21
      | ~ r1_tarski(k2_tarski(A_21,B_22),k1_tarski(C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_18,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k1_tarski(A_9),k2_tarski(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_20])).

tff(c_72,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | ~ r1_tarski(B_25,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1')
    | ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_81,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_74])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:53:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.17  
% 1.59/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.17  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.59/1.17  
% 1.59/1.17  %Foreground sorts:
% 1.59/1.17  
% 1.59/1.17  
% 1.59/1.17  %Background operators:
% 1.59/1.17  
% 1.59/1.17  
% 1.59/1.17  %Foreground operators:
% 1.59/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.59/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.17  
% 1.74/1.18  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.74/1.18  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.74/1.18  tff(f_39, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.74/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.74/1.18  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.18  tff(c_46, plain, (![C_20, A_21, B_22]: (C_20=A_21 | ~r1_tarski(k2_tarski(A_21, B_22), k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.18  tff(c_53, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_20, c_46])).
% 1.74/1.18  tff(c_18, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.18  tff(c_55, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18])).
% 1.74/1.18  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.18  tff(c_54, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_20])).
% 1.74/1.18  tff(c_72, plain, (![B_25, A_26]: (B_25=A_26 | ~r1_tarski(B_25, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.18  tff(c_74, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1') | ~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_72])).
% 1.74/1.18  tff(c_81, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_74])).
% 1.74/1.18  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_81])).
% 1.74/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  Inference rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Ref     : 0
% 1.74/1.18  #Sup     : 14
% 1.74/1.18  #Fact    : 0
% 1.74/1.18  #Define  : 0
% 1.74/1.18  #Split   : 0
% 1.74/1.18  #Chain   : 0
% 1.74/1.18  #Close   : 0
% 1.74/1.18  
% 1.74/1.18  Ordering : KBO
% 1.74/1.18  
% 1.74/1.18  Simplification rules
% 1.74/1.18  ----------------------
% 1.74/1.18  #Subsume      : 0
% 1.74/1.18  #Demod        : 5
% 1.74/1.18  #Tautology    : 10
% 1.74/1.18  #SimpNegUnit  : 1
% 1.74/1.18  #BackRed      : 2
% 1.74/1.18  
% 1.74/1.18  #Partial instantiations: 0
% 1.74/1.18  #Strategies tried      : 1
% 1.74/1.18  
% 1.74/1.18  Timing (in seconds)
% 1.74/1.18  ----------------------
% 1.74/1.18  Preprocessing        : 0.29
% 1.74/1.18  Parsing              : 0.16
% 1.74/1.18  CNF conversion       : 0.02
% 1.74/1.18  Main loop            : 0.09
% 1.74/1.18  Inferencing          : 0.03
% 1.74/1.18  Reduction            : 0.03
% 1.74/1.18  Demodulation         : 0.02
% 1.74/1.18  BG Simplification    : 0.01
% 1.74/1.18  Subsumption          : 0.01
% 1.74/1.18  Abstraction          : 0.00
% 1.74/1.18  MUC search           : 0.00
% 1.74/1.18  Cooper               : 0.00
% 1.74/1.18  Total                : 0.39
% 1.74/1.18  Index Insertion      : 0.00
% 1.74/1.18  Index Deletion       : 0.00
% 1.74/1.18  Index Matching       : 0.00
% 1.74/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
