%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:58 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   38 (  51 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 (  55 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_45,axiom,(
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

tff(c_122,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_198,plain,(
    ! [A_55,B_56] :
      ( '#skF_1'(k1_tarski(A_55),B_56) = A_55
      | r1_tarski(k1_tarski(A_55),B_56) ) ),
    inference(resolution,[status(thm)],[c_122,c_12])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_227,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(k1_tarski(A_59),B_60) = B_60
      | '#skF_1'(k1_tarski(A_59),B_60) = A_59 ) ),
    inference(resolution,[status(thm)],[c_198,c_10])).

tff(c_261,plain,(
    ! [B_61,A_62] :
      ( k2_xboole_0(B_61,k1_tarski(A_62)) = B_61
      | '#skF_1'(k1_tarski(A_62),B_61) = A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_2])).

tff(c_303,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_35])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_313,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_6])).

tff(c_325,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_313])).

tff(c_342,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_325,c_10])).

tff(c_349,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_2])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.06/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.27  
% 2.06/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.28  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.06/1.28  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.28  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.28  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.06/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.28  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.28  tff(c_35, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 2.06/1.28  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.28  tff(c_122, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.28  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.28  tff(c_198, plain, (![A_55, B_56]: ('#skF_1'(k1_tarski(A_55), B_56)=A_55 | r1_tarski(k1_tarski(A_55), B_56))), inference(resolution, [status(thm)], [c_122, c_12])).
% 2.06/1.28  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.28  tff(c_227, plain, (![A_59, B_60]: (k2_xboole_0(k1_tarski(A_59), B_60)=B_60 | '#skF_1'(k1_tarski(A_59), B_60)=A_59)), inference(resolution, [status(thm)], [c_198, c_10])).
% 2.06/1.28  tff(c_261, plain, (![B_61, A_62]: (k2_xboole_0(B_61, k1_tarski(A_62))=B_61 | '#skF_1'(k1_tarski(A_62), B_61)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_227, c_2])).
% 2.06/1.28  tff(c_303, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_261, c_35])).
% 2.06/1.28  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.28  tff(c_313, plain, (~r2_hidden('#skF_4', '#skF_5') | r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_303, c_6])).
% 2.06/1.28  tff(c_325, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_313])).
% 2.06/1.28  tff(c_342, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_325, c_10])).
% 2.06/1.28  tff(c_349, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_342, c_2])).
% 2.06/1.28  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_349])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 79
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 0
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 7
% 2.06/1.28  #Demod        : 11
% 2.06/1.28  #Tautology    : 45
% 2.06/1.28  #SimpNegUnit  : 1
% 2.06/1.28  #BackRed      : 1
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.31
% 2.06/1.28  Parsing              : 0.15
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.28  Main loop            : 0.21
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.07
% 2.06/1.28  Demodulation         : 0.05
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.03
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.54
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
