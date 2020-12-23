%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_50,axiom,(
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

tff(f_53,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [B_17,C_18,A_19] :
      ( r2_hidden(B_17,C_18)
      | ~ r1_tarski(k2_tarski(A_19,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [B_23,A_24] : r2_hidden(B_23,k2_tarski(A_24,B_23)) ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_78,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_34,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_tarski(A_13)) = k1_ordinal1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [D_28,B_29,A_30] :
      ( ~ r2_hidden(D_28,B_29)
      | r2_hidden(D_28,k2_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_124,plain,(
    ! [D_43,A_44] :
      ( ~ r2_hidden(D_43,k1_tarski(A_44))
      | r2_hidden(D_43,k1_ordinal1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_85])).

tff(c_128,plain,(
    ! [A_9] : r2_hidden(A_9,k1_ordinal1(A_9)) ),
    inference(resolution,[status(thm)],[c_78,c_124])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.40  
% 2.14/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.41  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2
% 2.14/1.41  
% 2.14/1.41  %Foreground sorts:
% 2.14/1.41  
% 2.14/1.41  
% 2.14/1.41  %Background operators:
% 2.14/1.41  
% 2.14/1.41  
% 2.14/1.41  %Foreground operators:
% 2.14/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.14/1.41  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.14/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.14/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.41  
% 2.27/1.42  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.42  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/1.42  tff(f_48, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.27/1.42  tff(f_50, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.27/1.42  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.27/1.42  tff(f_53, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.27/1.42  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.42  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.42  tff(c_57, plain, (![B_17, C_18, A_19]: (r2_hidden(B_17, C_18) | ~r1_tarski(k2_tarski(A_19, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.42  tff(c_75, plain, (![B_23, A_24]: (r2_hidden(B_23, k2_tarski(A_24, B_23)))), inference(resolution, [status(thm)], [c_24, c_57])).
% 2.27/1.42  tff(c_78, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_75])).
% 2.27/1.42  tff(c_34, plain, (![A_13]: (k2_xboole_0(A_13, k1_tarski(A_13))=k1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.42  tff(c_85, plain, (![D_28, B_29, A_30]: (~r2_hidden(D_28, B_29) | r2_hidden(D_28, k2_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.42  tff(c_124, plain, (![D_43, A_44]: (~r2_hidden(D_43, k1_tarski(A_44)) | r2_hidden(D_43, k1_ordinal1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_85])).
% 2.27/1.42  tff(c_128, plain, (![A_9]: (r2_hidden(A_9, k1_ordinal1(A_9)))), inference(resolution, [status(thm)], [c_78, c_124])).
% 2.27/1.42  tff(c_36, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.42  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_36])).
% 2.27/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.42  
% 2.27/1.42  Inference rules
% 2.27/1.42  ----------------------
% 2.27/1.42  #Ref     : 0
% 2.27/1.42  #Sup     : 19
% 2.27/1.42  #Fact    : 0
% 2.27/1.42  #Define  : 0
% 2.27/1.42  #Split   : 0
% 2.27/1.42  #Chain   : 0
% 2.27/1.42  #Close   : 0
% 2.27/1.42  
% 2.27/1.42  Ordering : KBO
% 2.27/1.42  
% 2.27/1.42  Simplification rules
% 2.27/1.42  ----------------------
% 2.27/1.42  #Subsume      : 1
% 2.27/1.42  #Demod        : 5
% 2.27/1.42  #Tautology    : 10
% 2.27/1.42  #SimpNegUnit  : 0
% 2.27/1.42  #BackRed      : 1
% 2.27/1.42  
% 2.27/1.42  #Partial instantiations: 0
% 2.27/1.42  #Strategies tried      : 1
% 2.27/1.42  
% 2.27/1.42  Timing (in seconds)
% 2.27/1.42  ----------------------
% 2.27/1.43  Preprocessing        : 0.46
% 2.27/1.43  Parsing              : 0.24
% 2.27/1.43  CNF conversion       : 0.03
% 2.27/1.43  Main loop            : 0.21
% 2.27/1.43  Inferencing          : 0.07
% 2.27/1.43  Reduction            : 0.06
% 2.27/1.43  Demodulation         : 0.05
% 2.27/1.43  BG Simplification    : 0.02
% 2.27/1.43  Subsumption          : 0.05
% 2.27/1.43  Abstraction          : 0.01
% 2.27/1.43  MUC search           : 0.00
% 2.27/1.43  Cooper               : 0.00
% 2.27/1.43  Total                : 0.71
% 2.27/1.43  Index Insertion      : 0.00
% 2.27/1.43  Index Deletion       : 0.00
% 2.27/1.43  Index Matching       : 0.00
% 2.27/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
