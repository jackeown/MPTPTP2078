%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_116,plain,(
    ! [A_53,B_54] : k2_xboole_0(k1_tarski(A_53),k1_tarski(B_54)) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_122,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_54])).

tff(c_74,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [B_46,A_45] : r2_hidden(B_46,k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_137,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_80])).

tff(c_28,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_153,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_137,c_28])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.88/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.88/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.88/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.88/1.18  
% 1.98/1.19  tff(f_66, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.98/1.19  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.98/1.19  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.98/1.19  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.98/1.19  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.98/1.19  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.19  tff(c_116, plain, (![A_53, B_54]: (k2_xboole_0(k1_tarski(A_53), k1_tarski(B_54))=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.19  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.19  tff(c_122, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_116, c_54])).
% 1.98/1.19  tff(c_74, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.19  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.19  tff(c_80, plain, (![B_46, A_45]: (r2_hidden(B_46, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 1.98/1.19  tff(c_137, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_80])).
% 1.98/1.19  tff(c_28, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.19  tff(c_153, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_137, c_28])).
% 1.98/1.19  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_153])).
% 1.98/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  Inference rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Ref     : 0
% 1.98/1.19  #Sup     : 25
% 1.98/1.19  #Fact    : 0
% 1.98/1.19  #Define  : 0
% 1.98/1.19  #Split   : 0
% 1.98/1.19  #Chain   : 0
% 1.98/1.19  #Close   : 0
% 1.98/1.19  
% 1.98/1.19  Ordering : KBO
% 1.98/1.19  
% 1.98/1.19  Simplification rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Subsume      : 0
% 1.98/1.19  #Demod        : 4
% 1.98/1.19  #Tautology    : 19
% 1.98/1.19  #SimpNegUnit  : 1
% 1.98/1.19  #BackRed      : 0
% 1.98/1.19  
% 1.98/1.19  #Partial instantiations: 0
% 1.98/1.19  #Strategies tried      : 1
% 1.98/1.19  
% 1.98/1.19  Timing (in seconds)
% 1.98/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.31
% 1.98/1.19  Parsing              : 0.16
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.13
% 1.98/1.19  Inferencing          : 0.04
% 1.98/1.19  Reduction            : 0.05
% 1.98/1.19  Demodulation         : 0.04
% 1.98/1.19  BG Simplification    : 0.01
% 1.98/1.19  Subsumption          : 0.03
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.47
% 1.98/1.19  Index Insertion      : 0.00
% 1.98/1.19  Index Deletion       : 0.00
% 1.98/1.19  Index Matching       : 0.00
% 1.98/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
