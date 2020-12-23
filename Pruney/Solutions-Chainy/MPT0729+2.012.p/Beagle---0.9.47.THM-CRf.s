%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 12.89s
% Output     : CNFRefutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 103 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_66,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_64,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    k1_ordinal1('#skF_5') = k1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [A_26] : r2_hidden(A_26,k1_ordinal1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_65])).

tff(c_54,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_tarski(A_24)) = k1_ordinal1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_345,plain,(
    ! [D_79,B_80,A_81] :
      ( r2_hidden(D_79,B_80)
      | r2_hidden(D_79,A_81)
      | ~ r2_hidden(D_79,k2_xboole_0(A_81,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_357,plain,(
    ! [D_79,A_24] :
      ( r2_hidden(D_79,k1_tarski(A_24))
      | r2_hidden(D_79,A_24)
      | ~ r2_hidden(D_79,k1_ordinal1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_345])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_374,plain,(
    ! [E_83,C_84,B_85,A_86] :
      ( E_83 = C_84
      | E_83 = B_85
      | E_83 = A_86
      | ~ r2_hidden(E_83,k1_enumset1(A_86,B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3078,plain,(
    ! [E_300,B_301,A_302] :
      ( E_300 = B_301
      | E_300 = A_302
      | E_300 = A_302
      | ~ r2_hidden(E_300,k2_tarski(A_302,B_301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_374])).

tff(c_20551,plain,(
    ! [E_1474,A_1475] :
      ( E_1474 = A_1475
      | E_1474 = A_1475
      | E_1474 = A_1475
      | ~ r2_hidden(E_1474,k1_tarski(A_1475)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3078])).

tff(c_20756,plain,(
    ! [D_1476,A_1477] :
      ( D_1476 = A_1477
      | r2_hidden(D_1476,A_1477)
      | ~ r2_hidden(D_1476,k1_ordinal1(A_1477)) ) ),
    inference(resolution,[status(thm)],[c_357,c_20551])).

tff(c_20921,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_20756])).

tff(c_20971,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_20921])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20976,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_20971,c_2])).

tff(c_56,plain,(
    ! [A_25] : r2_hidden(A_25,k1_ordinal1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20977,plain,(
    ! [D_1478] :
      ( D_1478 = '#skF_5'
      | r2_hidden(D_1478,'#skF_5')
      | ~ r2_hidden(D_1478,k1_ordinal1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_20756])).

tff(c_21147,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_20977])).

tff(c_21194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20976,c_58,c_21147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:57:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.89/5.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.43  
% 12.89/5.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.43  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 12.89/5.43  
% 12.89/5.43  %Foreground sorts:
% 12.89/5.43  
% 12.89/5.43  
% 12.89/5.43  %Background operators:
% 12.89/5.43  
% 12.89/5.43  
% 12.89/5.43  %Foreground operators:
% 12.89/5.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.89/5.43  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 12.89/5.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.89/5.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.89/5.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.89/5.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.89/5.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.89/5.43  tff('#skF_5', type, '#skF_5': $i).
% 12.89/5.43  tff('#skF_6', type, '#skF_6': $i).
% 12.89/5.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.89/5.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.89/5.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 12.89/5.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.89/5.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.89/5.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.89/5.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 12.89/5.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.89/5.43  
% 12.89/5.44  tff(f_71, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 12.89/5.44  tff(f_66, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 12.89/5.44  tff(f_64, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 12.89/5.44  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 12.89/5.44  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.89/5.44  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.89/5.44  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 12.89/5.44  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 12.89/5.44  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.89/5.44  tff(c_60, plain, (k1_ordinal1('#skF_5')=k1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.89/5.44  tff(c_65, plain, (![A_26]: (r2_hidden(A_26, k1_ordinal1(A_26)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.89/5.44  tff(c_68, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_65])).
% 12.89/5.44  tff(c_54, plain, (![A_24]: (k2_xboole_0(A_24, k1_tarski(A_24))=k1_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.89/5.44  tff(c_345, plain, (![D_79, B_80, A_81]: (r2_hidden(D_79, B_80) | r2_hidden(D_79, A_81) | ~r2_hidden(D_79, k2_xboole_0(A_81, B_80)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.89/5.44  tff(c_357, plain, (![D_79, A_24]: (r2_hidden(D_79, k1_tarski(A_24)) | r2_hidden(D_79, A_24) | ~r2_hidden(D_79, k1_ordinal1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_345])).
% 12.89/5.44  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.89/5.44  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.89/5.44  tff(c_374, plain, (![E_83, C_84, B_85, A_86]: (E_83=C_84 | E_83=B_85 | E_83=A_86 | ~r2_hidden(E_83, k1_enumset1(A_86, B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.89/5.44  tff(c_3078, plain, (![E_300, B_301, A_302]: (E_300=B_301 | E_300=A_302 | E_300=A_302 | ~r2_hidden(E_300, k2_tarski(A_302, B_301)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_374])).
% 12.89/5.44  tff(c_20551, plain, (![E_1474, A_1475]: (E_1474=A_1475 | E_1474=A_1475 | E_1474=A_1475 | ~r2_hidden(E_1474, k1_tarski(A_1475)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3078])).
% 12.89/5.44  tff(c_20756, plain, (![D_1476, A_1477]: (D_1476=A_1477 | r2_hidden(D_1476, A_1477) | ~r2_hidden(D_1476, k1_ordinal1(A_1477)))), inference(resolution, [status(thm)], [c_357, c_20551])).
% 12.89/5.44  tff(c_20921, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_20756])).
% 12.89/5.44  tff(c_20971, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_20921])).
% 12.89/5.44  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 12.89/5.44  tff(c_20976, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_20971, c_2])).
% 12.89/5.44  tff(c_56, plain, (![A_25]: (r2_hidden(A_25, k1_ordinal1(A_25)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.89/5.44  tff(c_20977, plain, (![D_1478]: (D_1478='#skF_5' | r2_hidden(D_1478, '#skF_5') | ~r2_hidden(D_1478, k1_ordinal1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_20756])).
% 12.89/5.44  tff(c_21147, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_20977])).
% 12.89/5.44  tff(c_21194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20976, c_58, c_21147])).
% 12.89/5.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/5.44  
% 12.89/5.44  Inference rules
% 12.89/5.44  ----------------------
% 12.89/5.44  #Ref     : 0
% 12.89/5.44  #Sup     : 4519
% 12.89/5.44  #Fact    : 44
% 12.89/5.44  #Define  : 0
% 12.89/5.44  #Split   : 0
% 12.89/5.44  #Chain   : 0
% 12.89/5.44  #Close   : 0
% 12.89/5.44  
% 12.89/5.44  Ordering : KBO
% 12.89/5.44  
% 12.89/5.44  Simplification rules
% 12.89/5.44  ----------------------
% 12.89/5.44  #Subsume      : 1658
% 12.89/5.44  #Demod        : 673
% 12.89/5.44  #Tautology    : 93
% 12.89/5.44  #SimpNegUnit  : 78
% 12.89/5.44  #BackRed      : 146
% 12.89/5.45  
% 12.89/5.45  #Partial instantiations: 0
% 12.89/5.45  #Strategies tried      : 1
% 12.89/5.45  
% 12.89/5.45  Timing (in seconds)
% 12.89/5.45  ----------------------
% 12.89/5.45  Preprocessing        : 0.31
% 12.89/5.45  Parsing              : 0.15
% 12.89/5.45  CNF conversion       : 0.02
% 12.89/5.45  Main loop            : 4.39
% 12.89/5.45  Inferencing          : 0.88
% 12.89/5.45  Reduction            : 1.34
% 12.89/5.45  Demodulation         : 0.73
% 12.89/5.45  BG Simplification    : 0.10
% 12.89/5.45  Subsumption          : 1.74
% 12.89/5.45  Abstraction          : 0.14
% 12.89/5.45  MUC search           : 0.00
% 12.89/5.45  Cooper               : 0.00
% 12.89/5.45  Total                : 4.72
% 12.89/5.45  Index Insertion      : 0.00
% 12.89/5.45  Index Deletion       : 0.00
% 12.89/5.45  Index Matching       : 0.00
% 12.89/5.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
