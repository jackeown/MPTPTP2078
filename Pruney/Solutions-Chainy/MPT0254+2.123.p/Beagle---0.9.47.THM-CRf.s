%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_238,plain,(
    ! [A_60,B_61] :
      ( r1_xboole_0(A_60,B_61)
      | k4_xboole_0(A_60,B_61) != A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k2_xboole_0(A_47,B_48)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_94])).

tff(c_107,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_42,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    ! [D_42,A_43] : r2_hidden(D_42,k2_tarski(A_43,D_42)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_122,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_87])).

tff(c_127,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | ~ r1_xboole_0(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,(
    ! [B_51] :
      ( ~ r2_hidden('#skF_3',B_51)
      | ~ r1_xboole_0(k1_xboole_0,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_127])).

tff(c_159,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_122,c_143])).

tff(c_250,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_238,c_159])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.90/1.22  
% 1.90/1.22  %Foreground sorts:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Background operators:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Foreground operators:
% 1.90/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.22  
% 1.90/1.23  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.90/1.23  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.90/1.23  tff(f_75, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.90/1.23  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.90/1.23  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.23  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.90/1.23  tff(f_69, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.90/1.23  tff(c_10, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.23  tff(c_238, plain, (![A_60, B_61]: (r1_xboole_0(A_60, B_61) | k4_xboole_0(A_60, B_61)!=A_60)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.23  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.90/1.23  tff(c_94, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k2_xboole_0(A_47, B_48))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.23  tff(c_101, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_54, c_94])).
% 1.90/1.23  tff(c_107, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 1.90/1.23  tff(c_42, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.23  tff(c_84, plain, (![D_42, A_43]: (r2_hidden(D_42, k2_tarski(A_43, D_42)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.90/1.23  tff(c_87, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_84])).
% 1.90/1.23  tff(c_122, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_87])).
% 1.90/1.23  tff(c_127, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | ~r1_xboole_0(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.23  tff(c_143, plain, (![B_51]: (~r2_hidden('#skF_3', B_51) | ~r1_xboole_0(k1_xboole_0, B_51))), inference(superposition, [status(thm), theory('equality')], [c_107, c_127])).
% 1.90/1.23  tff(c_159, plain, (~r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_143])).
% 1.90/1.23  tff(c_250, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_238, c_159])).
% 1.90/1.23  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_250])).
% 1.90/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  Inference rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Ref     : 0
% 1.90/1.23  #Sup     : 53
% 1.90/1.23  #Fact    : 0
% 1.90/1.23  #Define  : 0
% 1.90/1.23  #Split   : 0
% 1.90/1.23  #Chain   : 0
% 1.90/1.23  #Close   : 0
% 1.90/1.23  
% 1.90/1.23  Ordering : KBO
% 1.90/1.23  
% 1.90/1.23  Simplification rules
% 1.90/1.23  ----------------------
% 1.90/1.23  #Subsume      : 3
% 1.90/1.23  #Demod        : 16
% 1.90/1.23  #Tautology    : 34
% 1.90/1.23  #SimpNegUnit  : 0
% 1.90/1.23  #BackRed      : 3
% 1.90/1.23  
% 1.90/1.23  #Partial instantiations: 0
% 1.90/1.23  #Strategies tried      : 1
% 1.90/1.23  
% 1.90/1.23  Timing (in seconds)
% 1.90/1.23  ----------------------
% 2.09/1.24  Preprocessing        : 0.31
% 2.09/1.24  Parsing              : 0.16
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.15
% 2.09/1.24  Inferencing          : 0.05
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.03
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.49
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
