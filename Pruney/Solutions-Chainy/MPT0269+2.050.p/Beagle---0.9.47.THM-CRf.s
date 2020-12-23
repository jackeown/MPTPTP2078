%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  37 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_26,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,k1_tarski(B_29)) = A_28
      | r2_hidden(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_30])).

tff(c_83,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_75])).

tff(c_107,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(k1_tarski(A_32),B_33) = B_33
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_87])).

tff(c_102,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_113,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_102])).

tff(c_122,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_113])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.46  
% 2.07/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.47  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.47  
% 2.21/1.47  %Foreground sorts:
% 2.21/1.47  
% 2.21/1.47  
% 2.21/1.47  %Background operators:
% 2.21/1.47  
% 2.21/1.47  
% 2.21/1.47  %Foreground operators:
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.47  
% 2.23/1.48  tff(f_62, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.23/1.48  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.23/1.48  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.23/1.48  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.23/1.48  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.23/1.48  tff(c_26, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.48  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.48  tff(c_69, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k1_tarski(B_29))=A_28 | r2_hidden(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.48  tff(c_30, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.48  tff(c_75, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_30])).
% 2.23/1.48  tff(c_83, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_28, c_75])).
% 2.23/1.48  tff(c_107, plain, (![A_32, B_33]: (k2_xboole_0(k1_tarski(A_32), B_33)=B_33 | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.48  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.48  tff(c_87, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.48  tff(c_99, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_87])).
% 2.23/1.48  tff(c_102, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_99])).
% 2.23/1.48  tff(c_113, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_102])).
% 2.23/1.48  tff(c_122, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_113])).
% 2.23/1.48  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_122])).
% 2.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.48  
% 2.23/1.48  Inference rules
% 2.23/1.48  ----------------------
% 2.23/1.48  #Ref     : 0
% 2.23/1.48  #Sup     : 24
% 2.23/1.48  #Fact    : 0
% 2.23/1.48  #Define  : 0
% 2.23/1.48  #Split   : 0
% 2.23/1.48  #Chain   : 0
% 2.23/1.48  #Close   : 0
% 2.23/1.48  
% 2.23/1.48  Ordering : KBO
% 2.23/1.48  
% 2.23/1.48  Simplification rules
% 2.23/1.48  ----------------------
% 2.23/1.48  #Subsume      : 0
% 2.23/1.48  #Demod        : 3
% 2.23/1.48  #Tautology    : 18
% 2.23/1.48  #SimpNegUnit  : 3
% 2.23/1.48  #BackRed      : 0
% 2.23/1.48  
% 2.23/1.48  #Partial instantiations: 0
% 2.23/1.48  #Strategies tried      : 1
% 2.23/1.48  
% 2.23/1.48  Timing (in seconds)
% 2.23/1.48  ----------------------
% 2.23/1.49  Preprocessing        : 0.48
% 2.23/1.49  Parsing              : 0.26
% 2.23/1.49  CNF conversion       : 0.03
% 2.23/1.49  Main loop            : 0.17
% 2.23/1.49  Inferencing          : 0.07
% 2.23/1.49  Reduction            : 0.05
% 2.23/1.49  Demodulation         : 0.03
% 2.23/1.49  BG Simplification    : 0.02
% 2.23/1.49  Subsumption          : 0.02
% 2.23/1.49  Abstraction          : 0.01
% 2.23/1.49  MUC search           : 0.00
% 2.23/1.49  Cooper               : 0.00
% 2.23/1.49  Total                : 0.69
% 2.23/1.49  Index Insertion      : 0.00
% 2.23/1.49  Index Deletion       : 0.00
% 2.23/1.49  Index Matching       : 0.00
% 2.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
