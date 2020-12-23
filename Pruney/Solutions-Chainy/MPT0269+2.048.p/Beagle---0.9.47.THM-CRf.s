%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:50 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_136,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,k1_tarski(B_38)) = A_37
      | r2_hidden(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_36])).

tff(c_150,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_142])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_300,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,k4_xboole_0(B_54,A_53)) = B_54
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_321,plain,
    ( k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_300])).

tff(c_325,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_321])).

tff(c_326,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_325])).

tff(c_329,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_326])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:57:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.04/1.26  
% 2.04/1.26  %Foreground sorts:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Background operators:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Foreground operators:
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.26  
% 2.04/1.26  tff(f_68, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.04/1.26  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.04/1.26  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.04/1.26  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.04/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.04/1.26  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.26  tff(c_136, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k1_tarski(B_38))=A_37 | r2_hidden(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.26  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.26  tff(c_142, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_36])).
% 2.04/1.26  tff(c_150, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_142])).
% 2.04/1.26  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.04/1.26  tff(c_32, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.26  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.26  tff(c_300, plain, (![A_53, B_54]: (k2_xboole_0(A_53, k4_xboole_0(B_54, A_53))=B_54 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.26  tff(c_321, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_300])).
% 2.04/1.26  tff(c_325, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_321])).
% 2.04/1.26  tff(c_326, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_325])).
% 2.04/1.26  tff(c_329, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_326])).
% 2.04/1.26  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_329])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.27  #Ref     : 0
% 2.04/1.27  #Sup     : 72
% 2.04/1.27  #Fact    : 0
% 2.04/1.27  #Define  : 0
% 2.04/1.27  #Split   : 0
% 2.04/1.27  #Chain   : 0
% 2.04/1.27  #Close   : 0
% 2.04/1.27  
% 2.04/1.27  Ordering : KBO
% 2.04/1.27  
% 2.04/1.27  Simplification rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Subsume      : 3
% 2.04/1.27  #Demod        : 16
% 2.04/1.27  #Tautology    : 54
% 2.04/1.27  #SimpNegUnit  : 3
% 2.04/1.27  #BackRed      : 1
% 2.04/1.27  
% 2.04/1.27  #Partial instantiations: 0
% 2.04/1.27  #Strategies tried      : 1
% 2.04/1.27  
% 2.04/1.27  Timing (in seconds)
% 2.04/1.27  ----------------------
% 2.04/1.27  Preprocessing        : 0.31
% 2.04/1.27  Parsing              : 0.17
% 2.04/1.27  CNF conversion       : 0.02
% 2.04/1.27  Main loop            : 0.19
% 2.04/1.27  Inferencing          : 0.08
% 2.04/1.27  Reduction            : 0.06
% 2.04/1.27  Demodulation         : 0.04
% 2.04/1.27  BG Simplification    : 0.01
% 2.04/1.27  Subsumption          : 0.02
% 2.04/1.27  Abstraction          : 0.01
% 2.04/1.27  MUC search           : 0.00
% 2.04/1.27  Cooper               : 0.00
% 2.04/1.27  Total                : 0.52
% 2.04/1.27  Index Insertion      : 0.00
% 2.04/1.27  Index Deletion       : 0.00
% 2.04/1.27  Index Matching       : 0.00
% 2.04/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
