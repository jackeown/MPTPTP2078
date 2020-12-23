%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
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
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:00:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1
% 1.62/1.12  
% 1.62/1.12  %Foreground sorts:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Background operators:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Foreground operators:
% 1.62/1.12  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.12  
% 1.62/1.12  tff(f_44, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.62/1.12  tff(f_33, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.62/1.12  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.62/1.12  tff(f_35, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.62/1.12  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.62/1.12  tff(c_14, plain, (k1_ordinal1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.12  tff(c_33, plain, (![A_14]: (k2_xboole_0(A_14, k1_tarski(A_14))=k1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.12  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.12  tff(c_45, plain, (![A_15]: (r1_tarski(A_15, k1_ordinal1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_2])).
% 1.62/1.12  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_45])).
% 1.62/1.12  tff(c_19, plain, (![A_10]: (r2_hidden(A_10, k1_ordinal1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.12  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_19])).
% 1.62/1.12  tff(c_49, plain, (![B_16, A_17]: (~r1_tarski(B_16, A_17) | ~r2_hidden(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.12  tff(c_52, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.62/1.12  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 1.62/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  Inference rules
% 1.62/1.12  ----------------------
% 1.62/1.12  #Ref     : 0
% 1.62/1.12  #Sup     : 11
% 1.62/1.12  #Fact    : 0
% 1.62/1.12  #Define  : 0
% 1.62/1.12  #Split   : 0
% 1.62/1.12  #Chain   : 0
% 1.62/1.12  #Close   : 0
% 1.62/1.12  
% 1.62/1.12  Ordering : KBO
% 1.62/1.12  
% 1.62/1.12  Simplification rules
% 1.62/1.12  ----------------------
% 1.62/1.12  #Subsume      : 0
% 1.62/1.12  #Demod        : 1
% 1.62/1.12  #Tautology    : 6
% 1.62/1.12  #SimpNegUnit  : 0
% 1.62/1.12  #BackRed      : 0
% 1.62/1.12  
% 1.62/1.12  #Partial instantiations: 0
% 1.62/1.12  #Strategies tried      : 1
% 1.62/1.12  
% 1.62/1.12  Timing (in seconds)
% 1.62/1.12  ----------------------
% 1.62/1.13  Preprocessing        : 0.28
% 1.62/1.13  Parsing              : 0.15
% 1.62/1.13  CNF conversion       : 0.01
% 1.62/1.13  Main loop            : 0.07
% 1.62/1.13  Inferencing          : 0.03
% 1.62/1.13  Reduction            : 0.02
% 1.62/1.13  Demodulation         : 0.02
% 1.62/1.13  BG Simplification    : 0.01
% 1.62/1.13  Subsumption          : 0.01
% 1.62/1.13  Abstraction          : 0.01
% 1.62/1.13  MUC search           : 0.00
% 1.62/1.13  Cooper               : 0.00
% 1.62/1.13  Total                : 0.37
% 1.62/1.13  Index Insertion      : 0.00
% 1.62/1.13  Index Deletion       : 0.00
% 1.62/1.13  Index Matching       : 0.00
% 1.62/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
