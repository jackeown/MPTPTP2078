%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

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
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_58,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_43,B_44] : k2_enumset1(A_43,A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [F_17,A_10,B_11,D_13] : r2_hidden(F_17,k2_enumset1(A_10,B_11,F_17,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_108,plain,(
    ! [A_45,B_46] : r2_hidden(A_45,k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_28])).

tff(c_111,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_108])).

tff(c_54,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_tarski(A_18)) = k1_ordinal1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | r2_hidden(D_37,k2_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [D_55,A_56] :
      ( ~ r2_hidden(D_55,k1_tarski(A_56))
      | r2_hidden(D_55,k1_ordinal1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_79])).

tff(c_141,plain,(
    ! [A_7] : r2_hidden(A_7,k1_ordinal1(A_7)) ),
    inference(resolution,[status(thm)],[c_111,c_137])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.58  
% 2.48/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.58  %$ r2_hidden > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 2.48/1.58  
% 2.48/1.58  %Foreground sorts:
% 2.48/1.58  
% 2.48/1.58  
% 2.48/1.58  %Background operators:
% 2.48/1.58  
% 2.48/1.58  
% 2.48/1.58  %Foreground operators:
% 2.48/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.58  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.48/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.48/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.58  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.48/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.58  
% 2.48/1.60  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.48/1.60  tff(f_38, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.48/1.60  tff(f_56, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.48/1.60  tff(f_58, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.48/1.60  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.48/1.60  tff(f_61, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.48/1.60  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.60  tff(c_87, plain, (![A_43, B_44]: (k2_enumset1(A_43, A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.60  tff(c_28, plain, (![F_17, A_10, B_11, D_13]: (r2_hidden(F_17, k2_enumset1(A_10, B_11, F_17, D_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.60  tff(c_108, plain, (![A_45, B_46]: (r2_hidden(A_45, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_28])).
% 2.48/1.60  tff(c_111, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_108])).
% 2.48/1.60  tff(c_54, plain, (![A_18]: (k2_xboole_0(A_18, k1_tarski(A_18))=k1_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.60  tff(c_79, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | r2_hidden(D_37, k2_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.60  tff(c_137, plain, (![D_55, A_56]: (~r2_hidden(D_55, k1_tarski(A_56)) | r2_hidden(D_55, k1_ordinal1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_79])).
% 2.48/1.60  tff(c_141, plain, (![A_7]: (r2_hidden(A_7, k1_ordinal1(A_7)))), inference(resolution, [status(thm)], [c_111, c_137])).
% 2.48/1.60  tff(c_56, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.60  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_56])).
% 2.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.60  
% 2.48/1.60  Inference rules
% 2.48/1.60  ----------------------
% 2.48/1.60  #Ref     : 0
% 2.48/1.60  #Sup     : 24
% 2.48/1.60  #Fact    : 0
% 2.48/1.60  #Define  : 0
% 2.48/1.60  #Split   : 0
% 2.48/1.60  #Chain   : 0
% 2.48/1.60  #Close   : 0
% 2.48/1.60  
% 2.48/1.60  Ordering : KBO
% 2.48/1.60  
% 2.48/1.60  Simplification rules
% 2.48/1.60  ----------------------
% 2.48/1.60  #Subsume      : 0
% 2.48/1.60  #Demod        : 4
% 2.48/1.60  #Tautology    : 15
% 2.48/1.60  #SimpNegUnit  : 0
% 2.48/1.60  #BackRed      : 1
% 2.48/1.60  
% 2.48/1.60  #Partial instantiations: 0
% 2.48/1.60  #Strategies tried      : 1
% 2.48/1.60  
% 2.48/1.60  Timing (in seconds)
% 2.48/1.60  ----------------------
% 2.48/1.60  Preprocessing        : 0.49
% 2.48/1.60  Parsing              : 0.23
% 2.48/1.60  CNF conversion       : 0.04
% 2.48/1.60  Main loop            : 0.26
% 2.48/1.60  Inferencing          : 0.08
% 2.48/1.60  Reduction            : 0.08
% 2.48/1.60  Demodulation         : 0.06
% 2.48/1.60  BG Simplification    : 0.02
% 2.48/1.60  Subsumption          : 0.06
% 2.48/1.60  Abstraction          : 0.02
% 2.48/1.61  MUC search           : 0.00
% 2.48/1.61  Cooper               : 0.00
% 2.48/1.61  Total                : 0.79
% 2.48/1.61  Index Insertion      : 0.00
% 2.48/1.61  Index Deletion       : 0.00
% 2.48/1.61  Index Matching       : 0.00
% 2.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
