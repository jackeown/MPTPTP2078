%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 (  70 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_28,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_45,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(k1_tarski(A_27),B_28)
      | r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,k1_tarski(A_36))
      | r2_hidden(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [B_46,A_47] :
      ( k4_xboole_0(B_46,k1_tarski(A_47)) = B_46
      | r2_hidden(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_72,c_6])).

tff(c_26,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_115,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_71])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_115])).

tff(c_128,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_216,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_30])).

tff(c_22,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_22])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_228])).

tff(c_240,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_241,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_286,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_32])).

tff(c_290,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_22])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:09:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.30  
% 2.02/1.30  %Foreground sorts:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Background operators:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Foreground operators:
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.30  
% 2.02/1.31  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.02/1.31  tff(f_48, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.02/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.02/1.31  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.02/1.31  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.02/1.31  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.31  tff(c_43, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.02/1.31  tff(c_45, plain, (![A_27, B_28]: (r1_xboole_0(k1_tarski(A_27), B_28) | r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.31  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.31  tff(c_72, plain, (![B_35, A_36]: (r1_xboole_0(B_35, k1_tarski(A_36)) | r2_hidden(A_36, B_35))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.02/1.31  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.31  tff(c_107, plain, (![B_46, A_47]: (k4_xboole_0(B_46, k1_tarski(A_47))=B_46 | r2_hidden(A_47, B_46))), inference(resolution, [status(thm)], [c_72, c_6])).
% 2.02/1.31  tff(c_26, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.31  tff(c_71, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_26])).
% 2.02/1.31  tff(c_115, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_71])).
% 2.02/1.31  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_115])).
% 2.02/1.31  tff(c_128, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.31  tff(c_129, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.31  tff(c_30, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.31  tff(c_216, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_30])).
% 2.02/1.31  tff(c_22, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.31  tff(c_228, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_22])).
% 2.02/1.31  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_228])).
% 2.02/1.31  tff(c_240, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.02/1.31  tff(c_241, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.02/1.31  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.31  tff(c_286, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_32])).
% 2.02/1.31  tff(c_290, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_286, c_22])).
% 2.02/1.31  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_290])).
% 2.02/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  Inference rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Ref     : 0
% 2.02/1.31  #Sup     : 64
% 2.02/1.31  #Fact    : 0
% 2.02/1.31  #Define  : 0
% 2.02/1.31  #Split   : 2
% 2.02/1.31  #Chain   : 0
% 2.02/1.31  #Close   : 0
% 2.02/1.31  
% 2.02/1.31  Ordering : KBO
% 2.02/1.31  
% 2.02/1.31  Simplification rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Subsume      : 9
% 2.02/1.31  #Demod        : 6
% 2.02/1.31  #Tautology    : 33
% 2.02/1.31  #SimpNegUnit  : 3
% 2.02/1.31  #BackRed      : 0
% 2.02/1.31  
% 2.02/1.31  #Partial instantiations: 0
% 2.02/1.31  #Strategies tried      : 1
% 2.02/1.31  
% 2.02/1.31  Timing (in seconds)
% 2.02/1.31  ----------------------
% 2.17/1.31  Preprocessing        : 0.32
% 2.17/1.31  Parsing              : 0.17
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.18
% 2.17/1.31  Inferencing          : 0.07
% 2.17/1.31  Reduction            : 0.05
% 2.17/1.31  Demodulation         : 0.03
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.03
% 2.17/1.31  Abstraction          : 0.01
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.53
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
