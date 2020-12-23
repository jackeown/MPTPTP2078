%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_35,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_21,plain,(
    ! [A_8] : r2_hidden(A_8,k1_ordinal1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_34,plain,(
    ! [B_10,A_11] :
      ( ~ r1_tarski(B_10,A_11)
      | ~ r2_hidden(A_11,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.12  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.58/1.12  
% 1.58/1.12  %Foreground sorts:
% 1.58/1.12  
% 1.58/1.12  
% 1.58/1.12  %Background operators:
% 1.58/1.12  
% 1.58/1.12  
% 1.58/1.12  %Foreground operators:
% 1.58/1.12  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.12  
% 1.58/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.58/1.12  tff(f_44, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.58/1.12  tff(f_35, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.58/1.12  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.58/1.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.12  tff(c_14, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.58/1.12  tff(c_21, plain, (![A_8]: (r2_hidden(A_8, k1_ordinal1(A_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.58/1.12  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_21])).
% 1.58/1.12  tff(c_34, plain, (![B_10, A_11]: (~r1_tarski(B_10, A_11) | ~r2_hidden(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.58/1.12  tff(c_37, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_34])).
% 1.58/1.12  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_37])).
% 1.58/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  Inference rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Ref     : 0
% 1.58/1.12  #Sup     : 7
% 1.58/1.12  #Fact    : 0
% 1.58/1.12  #Define  : 0
% 1.58/1.12  #Split   : 0
% 1.58/1.12  #Chain   : 0
% 1.58/1.12  #Close   : 0
% 1.58/1.12  
% 1.58/1.12  Ordering : KBO
% 1.58/1.12  
% 1.58/1.12  Simplification rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Subsume      : 0
% 1.58/1.12  #Demod        : 2
% 1.58/1.12  #Tautology    : 5
% 1.58/1.12  #SimpNegUnit  : 0
% 1.58/1.12  #BackRed      : 0
% 1.58/1.12  
% 1.58/1.12  #Partial instantiations: 0
% 1.58/1.12  #Strategies tried      : 1
% 1.58/1.12  
% 1.58/1.12  Timing (in seconds)
% 1.58/1.12  ----------------------
% 1.58/1.13  Preprocessing        : 0.25
% 1.58/1.13  Parsing              : 0.14
% 1.58/1.13  CNF conversion       : 0.01
% 1.58/1.13  Main loop            : 0.08
% 1.58/1.13  Inferencing          : 0.03
% 1.58/1.13  Reduction            : 0.02
% 1.58/1.13  Demodulation         : 0.02
% 1.58/1.13  BG Simplification    : 0.01
% 1.58/1.13  Subsumption          : 0.01
% 1.58/1.13  Abstraction          : 0.00
% 1.58/1.13  MUC search           : 0.00
% 1.58/1.13  Cooper               : 0.00
% 1.58/1.13  Total                : 0.34
% 1.58/1.13  Index Insertion      : 0.00
% 1.58/1.13  Index Deletion       : 0.00
% 1.58/1.13  Index Matching       : 0.00
% 1.58/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
