%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_33,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_14,plain,(
    k1_ordinal1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_tarski(A_14)) = k1_ordinal1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_15] : r1_tarski(A_15,k1_ordinal1(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_2])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_45])).

tff(c_19,plain,(
    ! [A_10] : r2_hidden(A_10,k1_ordinal1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_19])).

tff(c_49,plain,(
    ! [B_16,A_17] :
      ( ~ r1_tarski(B_16,A_17)
      | ~ r2_hidden(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.61/1.16  
% 1.61/1.16  %Foreground sorts:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Background operators:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Foreground operators:
% 1.61/1.16  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.61/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.16  
% 1.61/1.17  tff(f_44, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.61/1.17  tff(f_33, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.61/1.17  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.61/1.17  tff(f_35, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.61/1.17  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.61/1.17  tff(c_14, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.17  tff(c_33, plain, (![A_14]: (k2_xboole_0(A_14, k1_tarski(A_14))=k1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.17  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.17  tff(c_45, plain, (![A_15]: (r1_tarski(A_15, k1_ordinal1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_2])).
% 1.61/1.17  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_45])).
% 1.61/1.17  tff(c_19, plain, (![A_10]: (r2_hidden(A_10, k1_ordinal1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.17  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_19])).
% 1.61/1.17  tff(c_49, plain, (![B_16, A_17]: (~r1_tarski(B_16, A_17) | ~r2_hidden(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.17  tff(c_52, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.61/1.17  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 1.61/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  Inference rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Ref     : 0
% 1.61/1.17  #Sup     : 11
% 1.61/1.17  #Fact    : 0
% 1.61/1.17  #Define  : 0
% 1.61/1.17  #Split   : 0
% 1.61/1.17  #Chain   : 0
% 1.61/1.17  #Close   : 0
% 1.61/1.17  
% 1.61/1.17  Ordering : KBO
% 1.61/1.17  
% 1.61/1.17  Simplification rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Subsume      : 0
% 1.61/1.17  #Demod        : 1
% 1.61/1.17  #Tautology    : 6
% 1.61/1.17  #SimpNegUnit  : 0
% 1.61/1.17  #BackRed      : 0
% 1.61/1.17  
% 1.61/1.17  #Partial instantiations: 0
% 1.61/1.17  #Strategies tried      : 1
% 1.61/1.17  
% 1.61/1.17  Timing (in seconds)
% 1.61/1.17  ----------------------
% 1.61/1.17  Preprocessing        : 0.29
% 1.61/1.17  Parsing              : 0.15
% 1.61/1.17  CNF conversion       : 0.02
% 1.61/1.17  Main loop            : 0.07
% 1.61/1.17  Inferencing          : 0.03
% 1.61/1.17  Reduction            : 0.02
% 1.61/1.17  Demodulation         : 0.02
% 1.61/1.17  BG Simplification    : 0.01
% 1.61/1.17  Subsumption          : 0.01
% 1.61/1.17  Abstraction          : 0.01
% 1.61/1.17  MUC search           : 0.00
% 1.61/1.17  Cooper               : 0.00
% 1.61/1.17  Total                : 0.39
% 1.61/1.17  Index Insertion      : 0.00
% 1.61/1.17  Index Deletion       : 0.00
% 1.61/1.17  Index Matching       : 0.00
% 1.61/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
