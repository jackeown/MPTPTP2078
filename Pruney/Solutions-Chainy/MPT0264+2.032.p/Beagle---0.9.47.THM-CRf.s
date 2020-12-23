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
% DateTime   : Thu Dec  3 09:52:24 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  51 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(c_72,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_210,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,k3_xboole_0(A_71,B_72))
      | ~ r2_hidden(D_70,B_72)
      | ~ r2_hidden(D_70,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_262,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_86,'#skF_9')
      | ~ r2_hidden(D_86,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_210])).

tff(c_273,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_262])).

tff(c_280,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_273])).

tff(c_107,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    ! [A_34] : k1_enumset1(A_34,A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    ! [B_51] : k2_tarski(B_51,B_51) = k1_tarski(B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_70])).

tff(c_176,plain,(
    ! [D_63,B_64,A_65] :
      ( D_63 = B_64
      | D_63 = A_65
      | ~ r2_hidden(D_63,k2_tarski(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,(
    ! [D_63,B_51] :
      ( D_63 = B_51
      | D_63 = B_51
      | ~ r2_hidden(D_63,k1_tarski(B_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_176])).

tff(c_286,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_280,c_179])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_72,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.10/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.10/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_9', type, '#skF_9': $i).
% 2.10/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.10/1.26  
% 2.10/1.27  tff(f_77, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.10/1.27  tff(f_58, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.27  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.10/1.27  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.10/1.27  tff(f_68, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.10/1.27  tff(c_72, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.27  tff(c_74, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.27  tff(c_46, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_76, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.27  tff(c_210, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, k3_xboole_0(A_71, B_72)) | ~r2_hidden(D_70, B_72) | ~r2_hidden(D_70, A_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.27  tff(c_262, plain, (![D_86]: (r2_hidden(D_86, k1_tarski('#skF_7')) | ~r2_hidden(D_86, '#skF_9') | ~r2_hidden(D_86, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_210])).
% 2.10/1.27  tff(c_273, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_46, c_262])).
% 2.10/1.27  tff(c_280, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_273])).
% 2.10/1.27  tff(c_107, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.27  tff(c_70, plain, (![A_34]: (k1_enumset1(A_34, A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_123, plain, (![B_51]: (k2_tarski(B_51, B_51)=k1_tarski(B_51))), inference(superposition, [status(thm), theory('equality')], [c_107, c_70])).
% 2.10/1.27  tff(c_176, plain, (![D_63, B_64, A_65]: (D_63=B_64 | D_63=A_65 | ~r2_hidden(D_63, k2_tarski(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_179, plain, (![D_63, B_51]: (D_63=B_51 | D_63=B_51 | ~r2_hidden(D_63, k1_tarski(B_51)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_176])).
% 2.10/1.27  tff(c_286, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_280, c_179])).
% 2.10/1.27  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_72, c_286])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 47
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 0
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 2
% 2.10/1.27  #Demod        : 11
% 2.10/1.27  #Tautology    : 34
% 2.10/1.27  #SimpNegUnit  : 3
% 2.10/1.27  #BackRed      : 0
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.32
% 2.10/1.27  Parsing              : 0.15
% 2.10/1.27  CNF conversion       : 0.03
% 2.10/1.27  Main loop            : 0.19
% 2.10/1.27  Inferencing          : 0.06
% 2.10/1.27  Reduction            : 0.07
% 2.10/1.27  Demodulation         : 0.05
% 2.10/1.27  BG Simplification    : 0.02
% 2.10/1.27  Subsumption          : 0.04
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.53
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
