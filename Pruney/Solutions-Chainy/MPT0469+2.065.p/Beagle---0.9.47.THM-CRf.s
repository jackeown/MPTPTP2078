%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  62 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_46,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_202,plain,(
    ! [C_78,A_79] :
      ( r2_hidden(k4_tarski(C_78,'#skF_5'(A_79,k1_relat_1(A_79),C_78)),A_79)
      | ~ r2_hidden(C_78,k1_relat_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [B_52,C_53] : k4_xboole_0(k1_xboole_0,k2_tarski(B_52,C_53)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_54] : k4_xboole_0(k1_xboole_0,k1_tarski(A_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_8,plain,(
    ! [C_6,B_5] : ~ r2_hidden(C_6,k4_xboole_0(B_5,k1_tarski(C_6))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8])).

tff(c_226,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_202,c_73])).

tff(c_234,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_226])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_234])).

tff(c_240,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_496,plain,(
    ! [A_123,C_124] :
      ( r2_hidden(k4_tarski('#skF_9'(A_123,k2_relat_1(A_123),C_124),C_124),A_123)
      | ~ r2_hidden(C_124,k2_relat_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_248,plain,(
    ! [B_84,C_85] : k4_xboole_0(k1_xboole_0,k2_tarski(B_84,C_85)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_257,plain,(
    ! [A_86] : k4_xboole_0(k1_xboole_0,k1_tarski(A_86)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_248])).

tff(c_262,plain,(
    ! [A_86] : ~ r2_hidden(A_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_8])).

tff(c_520,plain,(
    ! [C_125] : ~ r2_hidden(C_125,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_496,c_262])).

tff(c_540,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_520])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.56  
% 2.39/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.56  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 2.39/1.56  
% 2.39/1.56  %Foreground sorts:
% 2.39/1.56  
% 2.39/1.56  
% 2.39/1.56  %Background operators:
% 2.39/1.56  
% 2.39/1.56  
% 2.39/1.56  %Foreground operators:
% 2.39/1.56  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.39/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.39/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.39/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.39/1.56  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.39/1.56  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.39/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.56  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.39/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.39/1.56  
% 2.56/1.57  tff(f_77, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.56/1.57  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.56/1.57  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.56/1.57  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.57  tff(f_57, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.56/1.57  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.56/1.57  tff(f_73, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.56/1.57  tff(c_46, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.57  tff(c_56, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.56/1.57  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.57  tff(c_202, plain, (![C_78, A_79]: (r2_hidden(k4_tarski(C_78, '#skF_5'(A_79, k1_relat_1(A_79), C_78)), A_79) | ~r2_hidden(C_78, k1_relat_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.57  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.57  tff(c_59, plain, (![B_52, C_53]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_52, C_53))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.57  tff(c_68, plain, (![A_54]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.56/1.57  tff(c_8, plain, (![C_6, B_5]: (~r2_hidden(C_6, k4_xboole_0(B_5, k1_tarski(C_6))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.57  tff(c_73, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_68, c_8])).
% 2.56/1.57  tff(c_226, plain, (![C_80]: (~r2_hidden(C_80, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_202, c_73])).
% 2.56/1.57  tff(c_234, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_226])).
% 2.56/1.57  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_234])).
% 2.56/1.57  tff(c_240, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.56/1.57  tff(c_496, plain, (![A_123, C_124]: (r2_hidden(k4_tarski('#skF_9'(A_123, k2_relat_1(A_123), C_124), C_124), A_123) | ~r2_hidden(C_124, k2_relat_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.56/1.57  tff(c_248, plain, (![B_84, C_85]: (k4_xboole_0(k1_xboole_0, k2_tarski(B_84, C_85))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.57  tff(c_257, plain, (![A_86]: (k4_xboole_0(k1_xboole_0, k1_tarski(A_86))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_248])).
% 2.56/1.57  tff(c_262, plain, (![A_86]: (~r2_hidden(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_257, c_8])).
% 2.56/1.57  tff(c_520, plain, (![C_125]: (~r2_hidden(C_125, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_496, c_262])).
% 2.56/1.57  tff(c_540, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_520])).
% 2.56/1.57  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_540])).
% 2.56/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.57  
% 2.56/1.57  Inference rules
% 2.56/1.57  ----------------------
% 2.56/1.57  #Ref     : 0
% 2.56/1.57  #Sup     : 111
% 2.56/1.57  #Fact    : 0
% 2.56/1.57  #Define  : 0
% 2.56/1.57  #Split   : 1
% 2.56/1.57  #Chain   : 0
% 2.56/1.57  #Close   : 0
% 2.56/1.57  
% 2.56/1.57  Ordering : KBO
% 2.56/1.57  
% 2.56/1.57  Simplification rules
% 2.56/1.57  ----------------------
% 2.56/1.57  #Subsume      : 12
% 2.56/1.57  #Demod        : 17
% 2.56/1.57  #Tautology    : 55
% 2.56/1.57  #SimpNegUnit  : 10
% 2.56/1.57  #BackRed      : 0
% 2.56/1.57  
% 2.56/1.57  #Partial instantiations: 0
% 2.56/1.57  #Strategies tried      : 1
% 2.56/1.57  
% 2.56/1.57  Timing (in seconds)
% 2.56/1.57  ----------------------
% 2.56/1.57  Preprocessing        : 0.40
% 2.56/1.57  Parsing              : 0.20
% 2.56/1.57  CNF conversion       : 0.03
% 2.56/1.58  Main loop            : 0.26
% 2.56/1.58  Inferencing          : 0.10
% 2.56/1.58  Reduction            : 0.07
% 2.56/1.58  Demodulation         : 0.05
% 2.56/1.58  BG Simplification    : 0.02
% 2.56/1.58  Subsumption          : 0.04
% 2.56/1.58  Abstraction          : 0.02
% 2.56/1.58  MUC search           : 0.00
% 2.56/1.58  Cooper               : 0.00
% 2.56/1.58  Total                : 0.68
% 2.56/1.58  Index Insertion      : 0.00
% 2.56/1.58  Index Deletion       : 0.00
% 2.56/1.58  Index Matching       : 0.00
% 2.56/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
