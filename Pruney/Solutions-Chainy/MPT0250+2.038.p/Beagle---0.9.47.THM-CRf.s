%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_20,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_138,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_153,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_144])).

tff(c_36,plain,(
    ! [B_16,A_17] : k2_xboole_0(B_16,A_17) = k2_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_17,B_16] : r1_tarski(A_17,k2_xboole_0(B_16,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_85,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | ~ r1_tarski(k1_tarski(A_20),B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_20,B_16] : r2_hidden(A_20,k2_xboole_0(B_16,k1_tarski(A_20))) ),
    inference(resolution,[status(thm)],[c_51,c_85])).

tff(c_164,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_98])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.17  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.17  
% 1.78/1.18  tff(f_48, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.78/1.18  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.78/1.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.78/1.18  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.18  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.78/1.18  tff(c_20, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.78/1.18  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.18  tff(c_22, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.78/1.18  tff(c_24, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.78/1.18  tff(c_138, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.18  tff(c_144, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_138])).
% 1.78/1.18  tff(c_153, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_144])).
% 1.78/1.18  tff(c_36, plain, (![B_16, A_17]: (k2_xboole_0(B_16, A_17)=k2_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.18  tff(c_51, plain, (![A_17, B_16]: (r1_tarski(A_17, k2_xboole_0(B_16, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_10])).
% 1.78/1.18  tff(c_85, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | ~r1_tarski(k1_tarski(A_20), B_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.18  tff(c_98, plain, (![A_20, B_16]: (r2_hidden(A_20, k2_xboole_0(B_16, k1_tarski(A_20))))), inference(resolution, [status(thm)], [c_51, c_85])).
% 1.78/1.18  tff(c_164, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_153, c_98])).
% 1.78/1.18  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_164])).
% 1.78/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  Inference rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Ref     : 0
% 1.78/1.18  #Sup     : 34
% 1.78/1.18  #Fact    : 0
% 1.78/1.18  #Define  : 0
% 1.78/1.18  #Split   : 0
% 1.78/1.18  #Chain   : 0
% 1.78/1.18  #Close   : 0
% 1.78/1.18  
% 1.78/1.18  Ordering : KBO
% 1.78/1.18  
% 1.78/1.18  Simplification rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Subsume      : 0
% 1.78/1.18  #Demod        : 13
% 1.78/1.18  #Tautology    : 24
% 1.78/1.18  #SimpNegUnit  : 1
% 1.78/1.18  #BackRed      : 1
% 1.78/1.18  
% 1.78/1.18  #Partial instantiations: 0
% 1.78/1.18  #Strategies tried      : 1
% 1.78/1.18  
% 1.78/1.18  Timing (in seconds)
% 1.78/1.18  ----------------------
% 1.78/1.18  Preprocessing        : 0.27
% 1.78/1.18  Parsing              : 0.14
% 1.78/1.18  CNF conversion       : 0.01
% 1.78/1.18  Main loop            : 0.13
% 1.78/1.18  Inferencing          : 0.05
% 1.78/1.18  Reduction            : 0.05
% 1.78/1.18  Demodulation         : 0.04
% 1.78/1.18  BG Simplification    : 0.01
% 1.78/1.18  Subsumption          : 0.02
% 1.78/1.18  Abstraction          : 0.01
% 1.78/1.18  MUC search           : 0.00
% 1.78/1.18  Cooper               : 0.00
% 1.78/1.19  Total                : 0.42
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
