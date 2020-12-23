%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_24,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,k1_tarski(B_35)) = A_34
      | r2_hidden(B_35,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_28])).

tff(c_122,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_113])).

tff(c_62,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tarski(A_26),B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(k1_tarski(A_39),B_40) = B_40
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_83,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80])).

tff(c_141,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_83])).

tff(c_150,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_141])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.19  
% 1.81/1.19  %Foreground sorts:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Background operators:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Foreground operators:
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.19  
% 1.81/1.20  tff(f_60, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.81/1.20  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.81/1.20  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.81/1.20  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.81/1.20  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.81/1.20  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.81/1.20  tff(c_24, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.20  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.20  tff(c_101, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k1_tarski(B_35))=A_34 | r2_hidden(B_35, A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.20  tff(c_28, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.20  tff(c_113, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_28])).
% 1.81/1.20  tff(c_122, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_26, c_113])).
% 1.81/1.20  tff(c_62, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.20  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.20  tff(c_135, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)=B_40 | ~r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_62, c_4])).
% 1.81/1.20  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.20  tff(c_71, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.20  tff(c_80, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_71])).
% 1.81/1.20  tff(c_83, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80])).
% 1.81/1.20  tff(c_141, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_83])).
% 1.81/1.20  tff(c_150, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_141])).
% 1.81/1.20  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_150])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 30
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 0
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 1
% 1.81/1.20  #Demod        : 3
% 1.81/1.20  #Tautology    : 22
% 1.81/1.20  #SimpNegUnit  : 3
% 1.81/1.20  #BackRed      : 0
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.21  Preprocessing        : 0.29
% 1.81/1.21  Parsing              : 0.16
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.12
% 1.81/1.21  Inferencing          : 0.05
% 1.81/1.21  Reduction            : 0.03
% 1.81/1.21  Demodulation         : 0.02
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.01
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.43
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
