%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_47,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_45,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_22])).

tff(c_40,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_tarski(A_14)) = k1_ordinal1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [D_22,B_23,A_24] :
      ( ~ r2_hidden(D_22,B_23)
      | r2_hidden(D_22,k2_xboole_0(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [D_35,A_36] :
      ( ~ r2_hidden(D_35,k1_tarski(A_36))
      | r2_hidden(D_35,k1_ordinal1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_71])).

tff(c_108,plain,(
    ! [A_19] : r2_hidden(A_19,k1_ordinal1(A_19)) ),
    inference(resolution,[status(thm)],[c_51,c_104])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.58  
% 2.19/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.59  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 2.19/1.59  
% 2.19/1.59  %Foreground sorts:
% 2.19/1.59  
% 2.19/1.59  
% 2.19/1.59  %Background operators:
% 2.19/1.59  
% 2.19/1.59  
% 2.19/1.59  %Foreground operators:
% 2.19/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.59  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.19/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.19/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.59  
% 2.19/1.60  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.60  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.19/1.60  tff(f_47, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.19/1.60  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.19/1.60  tff(f_50, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.19/1.60  tff(c_45, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.60  tff(c_22, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.60  tff(c_51, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_22])).
% 2.19/1.60  tff(c_40, plain, (![A_14]: (k2_xboole_0(A_14, k1_tarski(A_14))=k1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.60  tff(c_71, plain, (![D_22, B_23, A_24]: (~r2_hidden(D_22, B_23) | r2_hidden(D_22, k2_xboole_0(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.60  tff(c_104, plain, (![D_35, A_36]: (~r2_hidden(D_35, k1_tarski(A_36)) | r2_hidden(D_35, k1_ordinal1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_71])).
% 2.19/1.60  tff(c_108, plain, (![A_19]: (r2_hidden(A_19, k1_ordinal1(A_19)))), inference(resolution, [status(thm)], [c_51, c_104])).
% 2.19/1.60  tff(c_42, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.60  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_42])).
% 2.19/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.60  
% 2.19/1.60  Inference rules
% 2.19/1.60  ----------------------
% 2.19/1.60  #Ref     : 0
% 2.19/1.60  #Sup     : 14
% 2.19/1.60  #Fact    : 0
% 2.19/1.60  #Define  : 0
% 2.19/1.60  #Split   : 0
% 2.19/1.60  #Chain   : 0
% 2.19/1.60  #Close   : 0
% 2.19/1.60  
% 2.19/1.60  Ordering : KBO
% 2.19/1.60  
% 2.19/1.60  Simplification rules
% 2.19/1.60  ----------------------
% 2.19/1.60  #Subsume      : 0
% 2.19/1.60  #Demod        : 2
% 2.19/1.60  #Tautology    : 8
% 2.19/1.60  #SimpNegUnit  : 0
% 2.19/1.60  #BackRed      : 1
% 2.19/1.60  
% 2.19/1.60  #Partial instantiations: 0
% 2.19/1.60  #Strategies tried      : 1
% 2.19/1.60  
% 2.19/1.60  Timing (in seconds)
% 2.19/1.60  ----------------------
% 2.19/1.60  Preprocessing        : 0.46
% 2.19/1.60  Parsing              : 0.21
% 2.19/1.60  CNF conversion       : 0.04
% 2.19/1.60  Main loop            : 0.19
% 2.19/1.60  Inferencing          : 0.06
% 2.19/1.60  Reduction            : 0.06
% 2.19/1.60  Demodulation         : 0.05
% 2.19/1.60  BG Simplification    : 0.02
% 2.19/1.60  Subsumption          : 0.04
% 2.19/1.60  Abstraction          : 0.02
% 2.19/1.60  MUC search           : 0.00
% 2.19/1.60  Cooper               : 0.00
% 2.19/1.61  Total                : 0.69
% 2.19/1.61  Index Insertion      : 0.00
% 2.19/1.61  Index Deletion       : 0.00
% 2.19/1.61  Index Matching       : 0.00
% 2.19/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
