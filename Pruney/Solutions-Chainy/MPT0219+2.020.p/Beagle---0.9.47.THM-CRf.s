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
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_79,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_78,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_224,plain,(
    ! [A_96,B_97] : k2_xboole_0(k1_tarski(A_96),k1_tarski(B_97)) = k2_tarski(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_230,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_80])).

tff(c_181,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    ! [B_88,A_87] : r2_hidden(B_88,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_26])).

tff(c_252,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_193])).

tff(c_48,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_262,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_252,c_48])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.33/1.34  
% 2.33/1.34  %Foreground sorts:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Background operators:
% 2.33/1.34  
% 2.33/1.34  
% 2.33/1.34  %Foreground operators:
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.33/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.33/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/1.34  
% 2.33/1.35  tff(f_94, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.33/1.35  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.33/1.35  tff(f_79, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.33/1.35  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.33/1.35  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.33/1.35  tff(c_78, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.33/1.35  tff(c_224, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), k1_tarski(B_97))=k2_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.35  tff(c_80, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.33/1.35  tff(c_230, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_224, c_80])).
% 2.33/1.35  tff(c_181, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.35  tff(c_26, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.35  tff(c_193, plain, (![B_88, A_87]: (r2_hidden(B_88, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_26])).
% 2.33/1.35  tff(c_252, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_193])).
% 2.33/1.35  tff(c_48, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.35  tff(c_262, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_252, c_48])).
% 2.33/1.35  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_262])).
% 2.33/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.35  
% 2.33/1.35  Inference rules
% 2.33/1.35  ----------------------
% 2.33/1.35  #Ref     : 0
% 2.33/1.35  #Sup     : 44
% 2.33/1.35  #Fact    : 0
% 2.33/1.35  #Define  : 0
% 2.33/1.35  #Split   : 0
% 2.33/1.35  #Chain   : 0
% 2.33/1.35  #Close   : 0
% 2.33/1.35  
% 2.33/1.35  Ordering : KBO
% 2.33/1.35  
% 2.33/1.35  Simplification rules
% 2.33/1.35  ----------------------
% 2.33/1.35  #Subsume      : 0
% 2.33/1.35  #Demod        : 7
% 2.33/1.35  #Tautology    : 38
% 2.33/1.35  #SimpNegUnit  : 1
% 2.33/1.35  #BackRed      : 0
% 2.33/1.35  
% 2.33/1.35  #Partial instantiations: 0
% 2.33/1.35  #Strategies tried      : 1
% 2.33/1.35  
% 2.33/1.35  Timing (in seconds)
% 2.33/1.35  ----------------------
% 2.33/1.35  Preprocessing        : 0.37
% 2.33/1.35  Parsing              : 0.20
% 2.33/1.35  CNF conversion       : 0.03
% 2.33/1.35  Main loop            : 0.16
% 2.33/1.35  Inferencing          : 0.04
% 2.33/1.35  Reduction            : 0.06
% 2.33/1.35  Demodulation         : 0.05
% 2.33/1.35  BG Simplification    : 0.02
% 2.33/1.35  Subsumption          : 0.03
% 2.33/1.35  Abstraction          : 0.01
% 2.33/1.35  MUC search           : 0.00
% 2.33/1.35  Cooper               : 0.00
% 2.33/1.35  Total                : 0.55
% 2.33/1.35  Index Insertion      : 0.00
% 2.33/1.35  Index Deletion       : 0.00
% 2.33/1.35  Index Matching       : 0.00
% 2.33/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
