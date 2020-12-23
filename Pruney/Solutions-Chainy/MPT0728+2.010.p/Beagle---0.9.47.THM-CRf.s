%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
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

tff(f_46,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_tarski(A_12)) = k1_ordinal1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [D_17,B_18,A_19] :
      ( ~ r2_hidden(D_17,B_18)
      | r2_hidden(D_17,k2_xboole_0(A_19,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [D_25,A_26] :
      ( ~ r2_hidden(D_25,k1_tarski(A_26))
      | r2_hidden(D_25,k1_ordinal1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_51])).

tff(c_68,plain,(
    ! [C_11] : r2_hidden(C_11,k1_ordinal1(C_11)) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.21  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.82/1.21  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.82/1.22  
% 1.82/1.22  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.82/1.22  tff(f_43, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.82/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.82/1.22  tff(f_46, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.82/1.22  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.22  tff(c_32, plain, (![A_12]: (k2_xboole_0(A_12, k1_tarski(A_12))=k1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.22  tff(c_51, plain, (![D_17, B_18, A_19]: (~r2_hidden(D_17, B_18) | r2_hidden(D_17, k2_xboole_0(A_19, B_18)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.82/1.22  tff(c_64, plain, (![D_25, A_26]: (~r2_hidden(D_25, k1_tarski(A_26)) | r2_hidden(D_25, k1_ordinal1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_51])).
% 1.82/1.22  tff(c_68, plain, (![C_11]: (r2_hidden(C_11, k1_ordinal1(C_11)))), inference(resolution, [status(thm)], [c_22, c_64])).
% 1.82/1.22  tff(c_34, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.22  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 15
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 0
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 0
% 1.82/1.22  #Demod        : 1
% 1.82/1.22  #Tautology    : 5
% 1.82/1.22  #SimpNegUnit  : 0
% 1.82/1.22  #BackRed      : 1
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 88
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.22  Preprocessing        : 0.26
% 1.82/1.22  Parsing              : 0.13
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.14
% 1.82/1.23  Inferencing          : 0.07
% 1.82/1.23  Reduction            : 0.03
% 1.82/1.23  Demodulation         : 0.02
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.02
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.42
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
