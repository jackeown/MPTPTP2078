%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   17 (  27 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_198,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,k1_tarski(B_48)) = A_47
      | r2_hidden(B_48,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_36])).

tff(c_228,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_214])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_300,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k2_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_370,plain,(
    ! [A_64,C_65] :
      ( r1_tarski(k1_tarski(A_64),C_65)
      | ~ r2_hidden(A_64,C_65)
      | ~ r2_hidden(A_64,C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_300])).

tff(c_32,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_269,plain,
    ( k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_248])).

tff(c_275,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_269])).

tff(c_276,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_275])).

tff(c_373,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_370,c_276])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  
% 2.07/1.25  tff(f_68, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.07/1.25  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.07/1.25  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.25  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.07/1.25  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.07/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.07/1.25  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.25  tff(c_198, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k1_tarski(B_48))=A_47 | r2_hidden(B_48, A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.25  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.25  tff(c_214, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_198, c_36])).
% 2.07/1.25  tff(c_228, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_214])).
% 2.07/1.25  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.25  tff(c_300, plain, (![A_57, B_58, C_59]: (r1_tarski(k2_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.25  tff(c_370, plain, (![A_64, C_65]: (r1_tarski(k1_tarski(A_64), C_65) | ~r2_hidden(A_64, C_65) | ~r2_hidden(A_64, C_65))), inference(superposition, [status(thm), theory('equality')], [c_14, c_300])).
% 2.07/1.25  tff(c_32, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.25  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.25  tff(c_248, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k4_xboole_0(B_51, A_50))=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.25  tff(c_269, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_248])).
% 2.07/1.25  tff(c_275, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_269])).
% 2.07/1.25  tff(c_276, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_275])).
% 2.07/1.25  tff(c_373, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_370, c_276])).
% 2.07/1.25  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_373])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 86
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 4
% 2.07/1.25  #Demod        : 26
% 2.07/1.25  #Tautology    : 58
% 2.07/1.25  #SimpNegUnit  : 3
% 2.07/1.25  #BackRed      : 0
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.28
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.20
% 2.07/1.25  Inferencing          : 0.08
% 2.07/1.25  Reduction            : 0.06
% 2.07/1.25  Demodulation         : 0.05
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.02
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.50
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
