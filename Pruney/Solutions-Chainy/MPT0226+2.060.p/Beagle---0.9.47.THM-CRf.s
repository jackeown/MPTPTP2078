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
% DateTime   : Thu Dec  3 09:48:45 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   50 (  53 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  52 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_74,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [D_24,A_19] : r2_hidden(D_24,k2_tarski(A_19,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_188,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_214,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_197])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_252,plain,(
    ! [D_83,A_84] :
      ( ~ r2_hidden(D_83,A_84)
      | ~ r2_hidden(D_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_4])).

tff(c_262,plain,(
    ! [D_24] : ~ r2_hidden(D_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_76,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_579,plain,(
    ! [D_1495,A_1496,B_1497] :
      ( r2_hidden(D_1495,k4_xboole_0(A_1496,B_1497))
      | r2_hidden(D_1495,B_1497)
      | ~ r2_hidden(D_1495,A_1496) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_595,plain,(
    ! [D_1495] :
      ( r2_hidden(D_1495,k1_xboole_0)
      | r2_hidden(D_1495,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_1495,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_579])).

tff(c_601,plain,(
    ! [D_1556] :
      ( r2_hidden(D_1556,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_1556,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_595])).

tff(c_630,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_32,c_601])).

tff(c_30,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_633,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_630,c_30])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:16:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 2.55/1.37  
% 2.55/1.37  %Foreground sorts:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Background operators:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Foreground operators:
% 2.55/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.55/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.55/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.55/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.55/1.37  
% 2.55/1.38  tff(f_80, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.55/1.38  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.55/1.38  tff(f_61, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.55/1.38  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.55/1.38  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.55/1.38  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.55/1.38  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.55/1.38  tff(c_74, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.55/1.38  tff(c_32, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.55/1.38  tff(c_44, plain, (![D_24, A_19]: (r2_hidden(D_24, k2_tarski(A_19, D_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.38  tff(c_28, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.38  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.38  tff(c_188, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.38  tff(c_197, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 2.55/1.38  tff(c_214, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_197])).
% 2.55/1.38  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.38  tff(c_252, plain, (![D_83, A_84]: (~r2_hidden(D_83, A_84) | ~r2_hidden(D_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_214, c_4])).
% 2.55/1.38  tff(c_262, plain, (![D_24]: (~r2_hidden(D_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_252])).
% 2.55/1.38  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.55/1.38  tff(c_579, plain, (![D_1495, A_1496, B_1497]: (r2_hidden(D_1495, k4_xboole_0(A_1496, B_1497)) | r2_hidden(D_1495, B_1497) | ~r2_hidden(D_1495, A_1496))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.38  tff(c_595, plain, (![D_1495]: (r2_hidden(D_1495, k1_xboole_0) | r2_hidden(D_1495, k1_tarski('#skF_8')) | ~r2_hidden(D_1495, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_579])).
% 2.55/1.38  tff(c_601, plain, (![D_1556]: (r2_hidden(D_1556, k1_tarski('#skF_8')) | ~r2_hidden(D_1556, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_262, c_595])).
% 2.55/1.38  tff(c_630, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_32, c_601])).
% 2.55/1.38  tff(c_30, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.55/1.38  tff(c_633, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_630, c_30])).
% 2.55/1.38  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_633])).
% 2.55/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  
% 2.55/1.38  Inference rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Ref     : 0
% 2.55/1.38  #Sup     : 79
% 2.55/1.38  #Fact    : 0
% 2.55/1.38  #Define  : 0
% 2.55/1.38  #Split   : 0
% 2.55/1.38  #Chain   : 0
% 2.55/1.38  #Close   : 0
% 2.55/1.38  
% 2.55/1.38  Ordering : KBO
% 2.55/1.38  
% 2.55/1.38  Simplification rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Subsume      : 11
% 2.55/1.38  #Demod        : 5
% 2.55/1.38  #Tautology    : 42
% 2.55/1.38  #SimpNegUnit  : 5
% 2.55/1.38  #BackRed      : 0
% 2.55/1.38  
% 2.55/1.38  #Partial instantiations: 520
% 2.55/1.38  #Strategies tried      : 1
% 2.55/1.38  
% 2.55/1.38  Timing (in seconds)
% 2.55/1.38  ----------------------
% 2.55/1.38  Preprocessing        : 0.31
% 2.55/1.38  Parsing              : 0.16
% 2.55/1.38  CNF conversion       : 0.03
% 2.55/1.38  Main loop            : 0.27
% 2.55/1.38  Inferencing          : 0.13
% 2.55/1.38  Reduction            : 0.07
% 2.55/1.38  Demodulation         : 0.05
% 2.55/1.38  BG Simplification    : 0.02
% 2.55/1.38  Subsumption          : 0.04
% 2.55/1.38  Abstraction          : 0.01
% 2.55/1.38  MUC search           : 0.00
% 2.55/1.38  Cooper               : 0.00
% 2.55/1.38  Total                : 0.61
% 2.55/1.38  Index Insertion      : 0.00
% 2.55/1.38  Index Deletion       : 0.00
% 2.55/1.38  Index Matching       : 0.00
% 2.55/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
