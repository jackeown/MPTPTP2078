%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  52 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [C_29,A_30,B_31] :
      ( k4_xboole_0(C_29,k2_tarski(A_30,B_31)) = C_29
      | r2_hidden(B_31,C_29)
      | r2_hidden(A_30,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [C_34,A_35] :
      ( k4_xboole_0(C_34,k1_tarski(A_35)) = C_34
      | r2_hidden(A_35,C_34)
      | r2_hidden(A_35,C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_16,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_tarski(A_15)) = k1_ordinal1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    ! [A_27,B_28] : k4_xboole_0(k2_xboole_0(A_27,B_28),B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_15] : k4_xboole_0(k1_ordinal1(A_15),k1_tarski(A_15)) = k4_xboole_0(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_86])).

tff(c_14,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_142,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_19])).

tff(c_186,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_142])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.20  
% 1.75/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.20  %$ r2_hidden > k2_enumset1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1
% 1.75/1.20  
% 1.75/1.20  %Foreground sorts:
% 1.75/1.20  
% 1.75/1.20  
% 1.75/1.20  %Background operators:
% 1.75/1.20  
% 1.75/1.20  
% 1.75/1.20  %Foreground operators:
% 1.75/1.20  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.75/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.20  
% 1.75/1.21  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.75/1.21  tff(f_48, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.75/1.21  tff(f_52, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.75/1.21  tff(f_32, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.75/1.21  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.75/1.21  tff(f_55, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 1.75/1.21  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.75/1.21  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.75/1.21  tff(c_101, plain, (![C_29, A_30, B_31]: (k4_xboole_0(C_29, k2_tarski(A_30, B_31))=C_29 | r2_hidden(B_31, C_29) | r2_hidden(A_30, C_29))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.75/1.21  tff(c_152, plain, (![C_34, A_35]: (k4_xboole_0(C_34, k1_tarski(A_35))=C_34 | r2_hidden(A_35, C_34) | r2_hidden(A_35, C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_101])).
% 1.75/1.21  tff(c_16, plain, (![A_15]: (k2_xboole_0(A_15, k1_tarski(A_15))=k1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.21  tff(c_86, plain, (![A_27, B_28]: (k4_xboole_0(k2_xboole_0(A_27, B_28), B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.21  tff(c_98, plain, (![A_15]: (k4_xboole_0(k1_ordinal1(A_15), k1_tarski(A_15))=k4_xboole_0(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_86])).
% 1.75/1.21  tff(c_14, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.21  tff(c_18, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.75/1.21  tff(c_19, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 1.75/1.21  tff(c_142, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_19])).
% 1.75/1.21  tff(c_186, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_152, c_142])).
% 1.75/1.21  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.75/1.21  tff(c_189, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_186, c_2])).
% 1.75/1.21  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_189])).
% 1.75/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  Inference rules
% 1.75/1.21  ----------------------
% 1.75/1.21  #Ref     : 0
% 1.75/1.21  #Sup     : 41
% 1.75/1.21  #Fact    : 0
% 1.75/1.21  #Define  : 0
% 1.75/1.21  #Split   : 0
% 1.75/1.21  #Chain   : 0
% 1.75/1.21  #Close   : 0
% 1.75/1.21  
% 1.75/1.21  Ordering : KBO
% 1.75/1.21  
% 1.75/1.21  Simplification rules
% 1.75/1.21  ----------------------
% 1.75/1.21  #Subsume      : 0
% 1.75/1.21  #Demod        : 4
% 1.75/1.21  #Tautology    : 25
% 1.75/1.21  #SimpNegUnit  : 0
% 1.75/1.21  #BackRed      : 1
% 1.75/1.21  
% 1.75/1.21  #Partial instantiations: 0
% 1.75/1.21  #Strategies tried      : 1
% 1.75/1.21  
% 1.75/1.21  Timing (in seconds)
% 1.75/1.21  ----------------------
% 1.75/1.21  Preprocessing        : 0.28
% 1.75/1.21  Parsing              : 0.16
% 1.75/1.21  CNF conversion       : 0.01
% 1.75/1.21  Main loop            : 0.13
% 1.75/1.21  Inferencing          : 0.06
% 1.75/1.21  Reduction            : 0.04
% 1.75/1.21  Demodulation         : 0.03
% 1.75/1.21  BG Simplification    : 0.01
% 1.75/1.21  Subsumption          : 0.01
% 1.75/1.21  Abstraction          : 0.01
% 1.75/1.21  MUC search           : 0.00
% 1.75/1.21  Cooper               : 0.00
% 1.75/1.21  Total                : 0.43
% 1.75/1.21  Index Insertion      : 0.00
% 1.75/1.21  Index Deletion       : 0.00
% 1.75/1.21  Index Matching       : 0.00
% 1.75/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
