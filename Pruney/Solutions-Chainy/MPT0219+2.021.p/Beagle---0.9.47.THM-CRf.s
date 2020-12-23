%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.28s
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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_76,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_229,plain,(
    ! [A_96,B_97] : k2_xboole_0(k1_tarski(A_96),k1_tarski(B_97)) = k2_tarski(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_78])).

tff(c_193,plain,(
    ! [A_88,B_89] : k1_enumset1(A_88,A_88,B_89) = k2_tarski(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_205,plain,(
    ! [B_89,A_88] : r2_hidden(B_89,k2_tarski(A_88,B_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_24])).

tff(c_257,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_205])).

tff(c_46,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_257,c_46])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.19  
% 2.28/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.20  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.28/1.20  
% 2.28/1.20  %Foreground sorts:
% 2.28/1.20  
% 2.28/1.20  
% 2.28/1.20  %Background operators:
% 2.28/1.20  
% 2.28/1.20  
% 2.28/1.20  %Foreground operators:
% 2.28/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.28/1.20  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.28/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.28/1.20  
% 2.28/1.20  tff(f_92, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.28/1.20  tff(f_71, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.28/1.20  tff(f_77, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.28/1.20  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.28/1.20  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.28/1.20  tff(c_76, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.28/1.20  tff(c_229, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), k1_tarski(B_97))=k2_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.20  tff(c_78, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.28/1.20  tff(c_239, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_229, c_78])).
% 2.28/1.20  tff(c_193, plain, (![A_88, B_89]: (k1_enumset1(A_88, A_88, B_89)=k2_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.28/1.20  tff(c_24, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.20  tff(c_205, plain, (![B_89, A_88]: (r2_hidden(B_89, k2_tarski(A_88, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_24])).
% 2.28/1.20  tff(c_257, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_205])).
% 2.28/1.20  tff(c_46, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.20  tff(c_267, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_257, c_46])).
% 2.28/1.20  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_267])).
% 2.28/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.20  
% 2.28/1.20  Inference rules
% 2.28/1.20  ----------------------
% 2.28/1.20  #Ref     : 0
% 2.28/1.20  #Sup     : 45
% 2.28/1.20  #Fact    : 0
% 2.28/1.20  #Define  : 0
% 2.28/1.20  #Split   : 0
% 2.28/1.20  #Chain   : 0
% 2.28/1.20  #Close   : 0
% 2.28/1.20  
% 2.28/1.20  Ordering : KBO
% 2.28/1.20  
% 2.28/1.20  Simplification rules
% 2.28/1.20  ----------------------
% 2.28/1.20  #Subsume      : 0
% 2.28/1.20  #Demod        : 8
% 2.28/1.20  #Tautology    : 39
% 2.28/1.20  #SimpNegUnit  : 1
% 2.28/1.20  #BackRed      : 0
% 2.28/1.20  
% 2.28/1.20  #Partial instantiations: 0
% 2.28/1.20  #Strategies tried      : 1
% 2.28/1.20  
% 2.28/1.20  Timing (in seconds)
% 2.28/1.20  ----------------------
% 2.28/1.21  Preprocessing        : 0.32
% 2.28/1.21  Parsing              : 0.16
% 2.28/1.21  CNF conversion       : 0.03
% 2.28/1.21  Main loop            : 0.16
% 2.28/1.21  Inferencing          : 0.04
% 2.28/1.21  Reduction            : 0.06
% 2.28/1.21  Demodulation         : 0.05
% 2.28/1.21  BG Simplification    : 0.02
% 2.28/1.21  Subsumption          : 0.03
% 2.28/1.21  Abstraction          : 0.01
% 2.28/1.21  MUC search           : 0.00
% 2.28/1.21  Cooper               : 0.00
% 2.28/1.21  Total                : 0.50
% 2.28/1.21  Index Insertion      : 0.00
% 2.28/1.21  Index Deletion       : 0.00
% 2.28/1.21  Index Matching       : 0.00
% 2.28/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
