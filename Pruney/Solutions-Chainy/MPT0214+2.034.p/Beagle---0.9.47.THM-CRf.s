%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:34 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  56 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_74,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_71])).

tff(c_90,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ r1_tarski(k1_tarski(A_47),B_48) ) ),
    inference(resolution,[status(thm)],[c_74,c_90])).

tff(c_131,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_121])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [E_50,C_51,B_52,A_53] :
      ( E_50 = C_51
      | E_50 = B_52
      | E_50 = A_53
      | ~ r2_hidden(E_50,k1_enumset1(A_53,B_52,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_217,plain,(
    ! [E_76,B_77,A_78] :
      ( E_76 = B_77
      | E_76 = A_78
      | E_76 = A_78
      | ~ r2_hidden(E_76,k2_tarski(A_78,B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_142])).

tff(c_236,plain,(
    ! [E_79,A_80] :
      ( E_79 = A_80
      | E_79 = A_80
      | E_79 = A_80
      | ~ r2_hidden(E_79,k1_tarski(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_217])).

tff(c_239,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131,c_236])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_38,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.19  
% 1.95/1.20  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.95/1.20  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.20  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.20  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.95/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.20  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.20  tff(c_40, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.20  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.20  tff(c_53, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.20  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.20  tff(c_71, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 1.95/1.20  tff(c_74, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_71])).
% 1.95/1.20  tff(c_90, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.20  tff(c_121, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~r1_tarski(k1_tarski(A_47), B_48))), inference(resolution, [status(thm)], [c_74, c_90])).
% 1.95/1.20  tff(c_131, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_121])).
% 1.95/1.20  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.95/1.20  tff(c_142, plain, (![E_50, C_51, B_52, A_53]: (E_50=C_51 | E_50=B_52 | E_50=A_53 | ~r2_hidden(E_50, k1_enumset1(A_53, B_52, C_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.20  tff(c_217, plain, (![E_76, B_77, A_78]: (E_76=B_77 | E_76=A_78 | E_76=A_78 | ~r2_hidden(E_76, k2_tarski(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_142])).
% 1.95/1.20  tff(c_236, plain, (![E_79, A_80]: (E_79=A_80 | E_79=A_80 | E_79=A_80 | ~r2_hidden(E_79, k1_tarski(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_217])).
% 1.95/1.20  tff(c_239, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_131, c_236])).
% 1.95/1.20  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_38, c_239])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 45
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 0
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 1.95/1.20  
% 1.95/1.20  Ordering : KBO
% 1.95/1.20  
% 1.95/1.20  Simplification rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Subsume      : 5
% 1.95/1.20  #Demod        : 9
% 1.95/1.20  #Tautology    : 20
% 1.95/1.20  #SimpNegUnit  : 1
% 1.95/1.20  #BackRed      : 0
% 1.95/1.20  
% 1.95/1.20  #Partial instantiations: 0
% 1.95/1.20  #Strategies tried      : 1
% 1.95/1.20  
% 1.95/1.20  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.20  Preprocessing        : 0.28
% 1.95/1.20  Parsing              : 0.14
% 1.95/1.20  CNF conversion       : 0.02
% 1.95/1.20  Main loop            : 0.16
% 1.95/1.20  Inferencing          : 0.06
% 1.95/1.20  Reduction            : 0.05
% 1.95/1.20  Demodulation         : 0.04
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.03
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.47
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
