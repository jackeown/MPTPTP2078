%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 ( 106 expanded)
%              Number of equality atoms :   19 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
          & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_212,plain,(
    ! [A_57,B_58,C_59] :
      ( k4_xboole_0(k2_tarski(A_57,B_58),C_59) = k1_xboole_0
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_270,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_34])).

tff(c_272,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_277,plain,(
    ! [B_60,C_61,A_62] :
      ( ~ r2_hidden(B_60,C_61)
      | k4_xboole_0(k2_tarski(A_62,B_60),C_61) = k1_tarski(A_62)
      | r2_hidden(A_62,C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_319,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_32])).

tff(c_345,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_319])).

tff(c_384,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_xboole_0(k2_tarski(A_72,B_73),C_74) = k2_tarski(A_72,B_73)
      | r2_hidden(B_73,C_74)
      | r2_hidden(A_72,C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_423,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_28])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_345,c_423])).

tff(c_458,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_459,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_515,plain,(
    ! [B_83,C_84,A_85] :
      ( ~ r2_hidden(B_83,C_84)
      | k4_xboole_0(k2_tarski(A_85,B_83),C_84) = k1_tarski(A_85)
      | r2_hidden(A_85,C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_722,plain,(
    ! [A_105,C_106,B_107] :
      ( ~ r2_hidden(A_105,C_106)
      | k4_xboole_0(k2_tarski(A_105,B_107),C_106) = k1_tarski(B_107)
      | r2_hidden(B_107,C_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_515])).

tff(c_30,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_770,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_30])).

tff(c_807,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_770])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.43  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.43  
% 2.62/1.43  %Foreground sorts:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Background operators:
% 2.62/1.43  
% 2.62/1.43  
% 2.62/1.43  %Foreground operators:
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.43  
% 2.62/1.44  tff(f_54, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 2.62/1.44  tff(f_68, negated_conjecture, ~(![A, B, C]: ~(((~(k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(B))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 2.62/1.44  tff(f_40, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.62/1.44  tff(f_48, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.62/1.44  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.62/1.44  tff(c_212, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k2_tarski(A_57, B_58), C_59)=k1_xboole_0 | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.44  tff(c_34, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.44  tff(c_270, plain, (~r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_212, c_34])).
% 2.62/1.44  tff(c_272, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_270])).
% 2.62/1.44  tff(c_277, plain, (![B_60, C_61, A_62]: (~r2_hidden(B_60, C_61) | k4_xboole_0(k2_tarski(A_62, B_60), C_61)=k1_tarski(A_62) | r2_hidden(A_62, C_61))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.44  tff(c_32, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.44  tff(c_319, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_277, c_32])).
% 2.62/1.44  tff(c_345, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_272, c_319])).
% 2.62/1.44  tff(c_384, plain, (![A_72, B_73, C_74]: (k4_xboole_0(k2_tarski(A_72, B_73), C_74)=k2_tarski(A_72, B_73) | r2_hidden(B_73, C_74) | r2_hidden(A_72, C_74))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.44  tff(c_28, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.44  tff(c_423, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_384, c_28])).
% 2.62/1.44  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_345, c_423])).
% 2.62/1.44  tff(c_458, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_270])).
% 2.62/1.44  tff(c_459, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_270])).
% 2.62/1.44  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.44  tff(c_515, plain, (![B_83, C_84, A_85]: (~r2_hidden(B_83, C_84) | k4_xboole_0(k2_tarski(A_85, B_83), C_84)=k1_tarski(A_85) | r2_hidden(A_85, C_84))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.62/1.44  tff(c_722, plain, (![A_105, C_106, B_107]: (~r2_hidden(A_105, C_106) | k4_xboole_0(k2_tarski(A_105, B_107), C_106)=k1_tarski(B_107) | r2_hidden(B_107, C_106))), inference(superposition, [status(thm), theory('equality')], [c_2, c_515])).
% 2.62/1.44  tff(c_30, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.44  tff(c_770, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_722, c_30])).
% 2.62/1.44  tff(c_807, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_770])).
% 2.62/1.44  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_807])).
% 2.62/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.44  
% 2.62/1.44  Inference rules
% 2.62/1.44  ----------------------
% 2.62/1.44  #Ref     : 0
% 2.62/1.44  #Sup     : 206
% 2.62/1.44  #Fact    : 2
% 2.62/1.44  #Define  : 0
% 2.62/1.44  #Split   : 3
% 2.62/1.44  #Chain   : 0
% 2.62/1.44  #Close   : 0
% 2.62/1.44  
% 2.62/1.44  Ordering : KBO
% 2.62/1.44  
% 2.62/1.44  Simplification rules
% 2.62/1.44  ----------------------
% 2.62/1.44  #Subsume      : 66
% 2.62/1.44  #Demod        : 24
% 2.62/1.44  #Tautology    : 82
% 2.62/1.44  #SimpNegUnit  : 12
% 2.62/1.44  #BackRed      : 0
% 2.62/1.44  
% 2.62/1.44  #Partial instantiations: 0
% 2.62/1.44  #Strategies tried      : 1
% 2.62/1.44  
% 2.62/1.44  Timing (in seconds)
% 2.62/1.44  ----------------------
% 2.92/1.44  Preprocessing        : 0.31
% 2.92/1.44  Parsing              : 0.16
% 2.92/1.44  CNF conversion       : 0.02
% 2.92/1.44  Main loop            : 0.36
% 2.92/1.44  Inferencing          : 0.14
% 2.92/1.44  Reduction            : 0.11
% 2.92/1.44  Demodulation         : 0.08
% 2.92/1.44  BG Simplification    : 0.02
% 2.92/1.44  Subsumption          : 0.07
% 2.92/1.44  Abstraction          : 0.02
% 2.92/1.45  MUC search           : 0.00
% 2.92/1.45  Cooper               : 0.00
% 2.92/1.45  Total                : 0.70
% 2.92/1.45  Index Insertion      : 0.00
% 2.92/1.45  Index Deletion       : 0.00
% 2.92/1.45  Index Matching       : 0.00
% 2.92/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
