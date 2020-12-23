%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 (  55 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_35,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_1'(A_33,B_34),A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    ! [A_51,B_52] :
      ( '#skF_1'(k1_tarski(A_51),B_52) = A_51
      | r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(resolution,[status(thm)],[c_95,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_199,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(k1_tarski(A_57),B_58) = B_58
      | '#skF_1'(k1_tarski(A_57),B_58) = A_57 ) ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_233,plain,(
    ! [B_59,A_60] :
      ( k2_xboole_0(B_59,k1_tarski(A_60)) = B_59
      | '#skF_1'(k1_tarski(A_60),B_59) = A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_2])).

tff(c_275,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_35])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_284,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_6])).

tff(c_296,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_284])).

tff(c_313,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_296,c_10])).

tff(c_321,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_2])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.25  
% 2.08/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.08/1.26  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.08/1.26  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.26  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.08/1.26  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.08/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.26  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.26  tff(c_35, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 2.08/1.26  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.26  tff(c_95, plain, (![A_33, B_34]: (r2_hidden('#skF_1'(A_33, B_34), A_33) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.26  tff(c_14, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.26  tff(c_166, plain, (![A_51, B_52]: ('#skF_1'(k1_tarski(A_51), B_52)=A_51 | r1_tarski(k1_tarski(A_51), B_52))), inference(resolution, [status(thm)], [c_95, c_14])).
% 2.08/1.26  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.08/1.26  tff(c_199, plain, (![A_57, B_58]: (k2_xboole_0(k1_tarski(A_57), B_58)=B_58 | '#skF_1'(k1_tarski(A_57), B_58)=A_57)), inference(resolution, [status(thm)], [c_166, c_10])).
% 2.08/1.26  tff(c_233, plain, (![B_59, A_60]: (k2_xboole_0(B_59, k1_tarski(A_60))=B_59 | '#skF_1'(k1_tarski(A_60), B_59)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_199, c_2])).
% 2.08/1.26  tff(c_275, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_233, c_35])).
% 2.08/1.26  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.26  tff(c_284, plain, (~r2_hidden('#skF_4', '#skF_5') | r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_275, c_6])).
% 2.08/1.26  tff(c_296, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_284])).
% 2.08/1.26  tff(c_313, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_296, c_10])).
% 2.08/1.26  tff(c_321, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_313, c_2])).
% 2.08/1.26  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_321])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 72
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 0
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 5
% 2.08/1.26  #Demod        : 10
% 2.08/1.26  #Tautology    : 41
% 2.08/1.26  #SimpNegUnit  : 1
% 2.08/1.26  #BackRed      : 0
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.26  Preprocessing        : 0.31
% 2.08/1.26  Parsing              : 0.16
% 2.08/1.26  CNF conversion       : 0.02
% 2.08/1.26  Main loop            : 0.19
% 2.08/1.26  Inferencing          : 0.08
% 2.08/1.26  Reduction            : 0.06
% 2.08/1.26  Demodulation         : 0.05
% 2.08/1.26  BG Simplification    : 0.01
% 2.08/1.26  Subsumption          : 0.03
% 2.08/1.26  Abstraction          : 0.01
% 2.08/1.26  MUC search           : 0.00
% 2.08/1.26  Cooper               : 0.00
% 2.08/1.26  Total                : 0.53
% 2.08/1.26  Index Insertion      : 0.00
% 2.08/1.26  Index Deletion       : 0.00
% 2.08/1.26  Index Matching       : 0.00
% 2.08/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
