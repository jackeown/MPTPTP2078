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

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  37 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
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

tff(c_22,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,k1_tarski(B_23)) = A_22
      | r2_hidden(B_23,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_26])).

tff(c_122,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_114])).

tff(c_251,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(k1_tarski(A_33),B_34) = B_34
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_73,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_257,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_73])).

tff(c_266,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_257])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  %$ r2_hidden > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.24  
% 1.88/1.24  %Foreground sorts:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Background operators:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Foreground operators:
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.24  
% 1.88/1.25  tff(f_58, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.88/1.25  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.88/1.25  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.88/1.25  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.88/1.25  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.88/1.25  tff(c_22, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.25  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.25  tff(c_105, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k1_tarski(B_23))=A_22 | r2_hidden(B_23, A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.25  tff(c_26, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.25  tff(c_114, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_26])).
% 1.88/1.25  tff(c_122, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_114])).
% 1.88/1.25  tff(c_251, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), B_34)=B_34 | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.25  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.25  tff(c_58, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.25  tff(c_67, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_58])).
% 1.88/1.25  tff(c_73, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 1.88/1.25  tff(c_257, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_251, c_73])).
% 1.88/1.25  tff(c_266, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_257])).
% 1.88/1.25  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_266])).
% 1.88/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.25  
% 1.88/1.25  Inference rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Ref     : 0
% 1.88/1.25  #Sup     : 64
% 1.88/1.25  #Fact    : 0
% 1.88/1.25  #Define  : 0
% 1.88/1.25  #Split   : 0
% 1.88/1.25  #Chain   : 0
% 1.88/1.25  #Close   : 0
% 1.88/1.25  
% 1.88/1.25  Ordering : KBO
% 1.88/1.25  
% 1.88/1.25  Simplification rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Subsume      : 1
% 1.88/1.25  #Demod        : 12
% 1.88/1.25  #Tautology    : 40
% 1.88/1.25  #SimpNegUnit  : 3
% 1.88/1.25  #BackRed      : 0
% 1.88/1.25  
% 1.88/1.25  #Partial instantiations: 0
% 1.88/1.25  #Strategies tried      : 1
% 1.88/1.25  
% 1.88/1.25  Timing (in seconds)
% 1.88/1.25  ----------------------
% 1.88/1.25  Preprocessing        : 0.27
% 1.88/1.25  Parsing              : 0.14
% 1.88/1.25  CNF conversion       : 0.02
% 1.88/1.25  Main loop            : 0.15
% 1.88/1.25  Inferencing          : 0.06
% 1.88/1.25  Reduction            : 0.05
% 1.88/1.25  Demodulation         : 0.04
% 1.88/1.25  BG Simplification    : 0.01
% 1.88/1.25  Subsumption          : 0.02
% 1.88/1.25  Abstraction          : 0.01
% 1.88/1.25  MUC search           : 0.00
% 1.88/1.25  Cooper               : 0.00
% 1.88/1.25  Total                : 0.44
% 1.88/1.25  Index Insertion      : 0.00
% 1.88/1.25  Index Deletion       : 0.00
% 1.88/1.25  Index Matching       : 0.00
% 1.88/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
