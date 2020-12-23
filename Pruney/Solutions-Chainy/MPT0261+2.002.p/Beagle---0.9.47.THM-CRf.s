%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_308,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k1_tarski(A_57),B_58) = k1_tarski(A_57)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_82,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_82])).

tff(c_95,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_12])).

tff(c_126,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_xboole_0(A_39,C_40)
      | ~ r1_tarski(A_39,k4_xboole_0(B_41,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_41,C_40] : r1_xboole_0(k4_xboole_0(B_41,C_40),C_40) ),
    inference(resolution,[status(thm)],[c_111,c_126])).

tff(c_363,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(k1_tarski(A_59),B_60)
      | r2_hidden(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_142])).

tff(c_26,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_369,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_363,c_26])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:46:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.16  
% 1.87/1.17  tff(f_58, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 1.87/1.17  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.87/1.17  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.87/1.17  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.87/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.87/1.17  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.87/1.17  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.87/1.17  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.87/1.17  tff(c_28, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.17  tff(c_308, plain, (![A_57, B_58]: (k4_xboole_0(k1_tarski(A_57), B_58)=k1_tarski(A_57) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.17  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.17  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.17  tff(c_49, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.17  tff(c_53, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_49])).
% 1.87/1.17  tff(c_82, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_91, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_53, c_82])).
% 1.87/1.17  tff(c_95, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_91])).
% 1.87/1.17  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.17  tff(c_111, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_95, c_12])).
% 1.87/1.17  tff(c_126, plain, (![A_39, C_40, B_41]: (r1_xboole_0(A_39, C_40) | ~r1_tarski(A_39, k4_xboole_0(B_41, C_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.17  tff(c_142, plain, (![B_41, C_40]: (r1_xboole_0(k4_xboole_0(B_41, C_40), C_40))), inference(resolution, [status(thm)], [c_111, c_126])).
% 1.87/1.17  tff(c_363, plain, (![A_59, B_60]: (r1_xboole_0(k1_tarski(A_59), B_60) | r2_hidden(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_308, c_142])).
% 1.87/1.17  tff(c_26, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.17  tff(c_369, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_363, c_26])).
% 1.87/1.17  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_369])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 80
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 0
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 1
% 1.87/1.17  #Demod        : 34
% 1.87/1.17  #Tautology    : 58
% 1.87/1.17  #SimpNegUnit  : 3
% 1.87/1.17  #BackRed      : 0
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.28
% 1.87/1.17  Parsing              : 0.15
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.17
% 1.87/1.17  Inferencing          : 0.07
% 1.87/1.17  Reduction            : 0.06
% 1.87/1.17  Demodulation         : 0.04
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.48
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
