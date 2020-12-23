%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:21 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  54 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_291,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_303,plain,(
    ! [B_59,A_58] : r2_hidden(B_59,k2_tarski(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_30])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_180,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_26,c_180])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_211,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_24])).

tff(c_337,plain,(
    ! [D_69,B_70,A_71] :
      ( ~ r2_hidden(D_69,B_70)
      | ~ r2_hidden(D_69,k4_xboole_0(A_71,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_341,plain,(
    ! [D_72,B_73] :
      ( ~ r2_hidden(D_72,B_73)
      | ~ r2_hidden(D_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_337])).

tff(c_354,plain,(
    ! [B_59] : ~ r2_hidden(B_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_303,c_341])).

tff(c_66,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_360,plain,(
    ! [B_74,A_75] :
      ( k1_tarski(B_74) = A_75
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_tarski(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_363,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_360])).

tff(c_376,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_363])).

tff(c_393,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_303])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.09/1.31  
% 2.09/1.31  %Foreground sorts:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Background operators:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Foreground operators:
% 2.09/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.31  
% 2.39/1.32  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.32  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.39/1.32  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.39/1.32  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.39/1.32  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.39/1.32  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.39/1.32  tff(f_79, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.39/1.32  tff(f_74, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.39/1.32  tff(c_291, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.32  tff(c_30, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.32  tff(c_303, plain, (![B_59, A_58]: (r2_hidden(B_59, k2_tarski(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_30])).
% 2.39/1.32  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.32  tff(c_180, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.32  tff(c_198, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), A_53)=A_53)), inference(resolution, [status(thm)], [c_26, c_180])).
% 2.39/1.32  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.32  tff(c_211, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_198, c_24])).
% 2.39/1.32  tff(c_337, plain, (![D_69, B_70, A_71]: (~r2_hidden(D_69, B_70) | ~r2_hidden(D_69, k4_xboole_0(A_71, B_70)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.32  tff(c_341, plain, (![D_72, B_73]: (~r2_hidden(D_72, B_73) | ~r2_hidden(D_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_337])).
% 2.39/1.32  tff(c_354, plain, (![B_59]: (~r2_hidden(B_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_303, c_341])).
% 2.39/1.32  tff(c_66, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.32  tff(c_68, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.39/1.32  tff(c_360, plain, (![B_74, A_75]: (k1_tarski(B_74)=A_75 | k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_tarski(B_74)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.32  tff(c_363, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_360])).
% 2.39/1.32  tff(c_376, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_363])).
% 2.39/1.32  tff(c_393, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_376, c_303])).
% 2.39/1.32  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_393])).
% 2.39/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  Inference rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Ref     : 0
% 2.39/1.32  #Sup     : 79
% 2.39/1.32  #Fact    : 0
% 2.39/1.32  #Define  : 0
% 2.39/1.32  #Split   : 0
% 2.39/1.32  #Chain   : 0
% 2.39/1.32  #Close   : 0
% 2.39/1.32  
% 2.39/1.32  Ordering : KBO
% 2.39/1.32  
% 2.39/1.32  Simplification rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Subsume      : 3
% 2.39/1.32  #Demod        : 26
% 2.39/1.32  #Tautology    : 56
% 2.39/1.32  #SimpNegUnit  : 2
% 2.39/1.32  #BackRed      : 4
% 2.39/1.32  
% 2.39/1.32  #Partial instantiations: 0
% 2.39/1.32  #Strategies tried      : 1
% 2.39/1.32  
% 2.39/1.32  Timing (in seconds)
% 2.39/1.32  ----------------------
% 2.39/1.32  Preprocessing        : 0.33
% 2.39/1.32  Parsing              : 0.16
% 2.39/1.32  CNF conversion       : 0.03
% 2.39/1.32  Main loop            : 0.22
% 2.39/1.32  Inferencing          : 0.07
% 2.39/1.32  Reduction            : 0.08
% 2.39/1.32  Demodulation         : 0.06
% 2.39/1.32  BG Simplification    : 0.02
% 2.39/1.32  Subsumption          : 0.04
% 2.39/1.32  Abstraction          : 0.01
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.58
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
