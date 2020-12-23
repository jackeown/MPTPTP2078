%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   25 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  34 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_tarski(A_7)) = k1_ordinal1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31,plain,(
    ! [B_13,A_14] :
      ( k4_xboole_0(k2_xboole_0(B_13,k1_tarski(A_14)),k1_tarski(A_14)) = B_13
      | r2_hidden(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_15] :
      ( k4_xboole_0(k1_ordinal1(A_15),k1_tarski(A_15)) = A_15
      | r2_hidden(A_15,A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_54,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_11])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.12  
% 1.54/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.13  %$ r2_hidden > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.54/1.13  
% 1.54/1.13  %Foreground sorts:
% 1.54/1.13  
% 1.54/1.13  
% 1.54/1.13  %Background operators:
% 1.54/1.13  
% 1.54/1.13  
% 1.54/1.13  %Foreground operators:
% 1.54/1.13  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.54/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.54/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.54/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.54/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.54/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.13  
% 1.65/1.13  tff(f_39, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.65/1.13  tff(f_35, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.65/1.13  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.65/1.13  tff(f_42, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.65/1.13  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.65/1.13  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_tarski(A_7))=k1_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.13  tff(c_31, plain, (![B_13, A_14]: (k4_xboole_0(k2_xboole_0(B_13, k1_tarski(A_14)), k1_tarski(A_14))=B_13 | r2_hidden(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.13  tff(c_43, plain, (![A_15]: (k4_xboole_0(k1_ordinal1(A_15), k1_tarski(A_15))=A_15 | r2_hidden(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 1.65/1.13  tff(c_6, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.13  tff(c_10, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.13  tff(c_11, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.65/1.13  tff(c_54, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_11])).
% 1.65/1.13  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.65/1.13  tff(c_57, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_2])).
% 1.65/1.13  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_57])).
% 1.65/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  Inference rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Ref     : 0
% 1.65/1.13  #Sup     : 11
% 1.65/1.13  #Fact    : 0
% 1.65/1.13  #Define  : 0
% 1.65/1.13  #Split   : 0
% 1.65/1.13  #Chain   : 0
% 1.65/1.13  #Close   : 0
% 1.65/1.13  
% 1.65/1.13  Ordering : KBO
% 1.65/1.13  
% 1.65/1.13  Simplification rules
% 1.65/1.13  ----------------------
% 1.65/1.13  #Subsume      : 0
% 1.65/1.13  #Demod        : 2
% 1.65/1.13  #Tautology    : 8
% 1.65/1.13  #SimpNegUnit  : 0
% 1.65/1.13  #BackRed      : 0
% 1.65/1.13  
% 1.65/1.13  #Partial instantiations: 0
% 1.65/1.13  #Strategies tried      : 1
% 1.65/1.13  
% 1.65/1.13  Timing (in seconds)
% 1.65/1.13  ----------------------
% 1.65/1.14  Preprocessing        : 0.25
% 1.65/1.14  Parsing              : 0.13
% 1.65/1.14  CNF conversion       : 0.01
% 1.65/1.14  Main loop            : 0.07
% 1.65/1.14  Inferencing          : 0.03
% 1.65/1.14  Reduction            : 0.02
% 1.65/1.14  Demodulation         : 0.02
% 1.65/1.14  BG Simplification    : 0.01
% 1.65/1.14  Subsumption          : 0.01
% 1.65/1.14  Abstraction          : 0.01
% 1.65/1.14  MUC search           : 0.00
% 1.65/1.14  Cooper               : 0.00
% 1.65/1.14  Total                : 0.34
% 1.65/1.14  Index Insertion      : 0.00
% 1.65/1.14  Index Deletion       : 0.00
% 1.65/1.14  Index Matching       : 0.00
% 1.65/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
