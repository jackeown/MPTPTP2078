%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:54 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  56 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

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

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_35,B_36] : r2_hidden(A_35,k2_tarski(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_76,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_92,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(resolution,[status(thm)],[c_76,c_92])).

tff(c_133,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_123])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_203,plain,(
    ! [E_76,C_77,B_78,A_79] :
      ( E_76 = C_77
      | E_76 = B_78
      | E_76 = A_79
      | ~ r2_hidden(E_76,k1_enumset1(A_79,B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_241,plain,(
    ! [E_83,B_84,A_85] :
      ( E_83 = B_84
      | E_83 = A_85
      | E_83 = A_85
      | ~ r2_hidden(E_83,k2_tarski(A_85,B_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_203])).

tff(c_265,plain,(
    ! [E_86,A_87] :
      ( E_86 = A_87
      | E_86 = A_87
      | E_86 = A_87
      | ~ r2_hidden(E_86,k1_tarski(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_241])).

tff(c_272,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_133,c_265])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.21  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.21  
% 1.99/1.22  tff(f_60, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.99/1.22  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.22  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.99/1.22  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.99/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.99/1.22  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.22  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.22  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.22  tff(c_55, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.22  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.22  tff(c_73, plain, (![A_35, B_36]: (r2_hidden(A_35, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 1.99/1.22  tff(c_76, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 1.99/1.22  tff(c_92, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.22  tff(c_123, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | ~r1_tarski(k1_tarski(A_51), B_52))), inference(resolution, [status(thm)], [c_76, c_92])).
% 1.99/1.22  tff(c_133, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_123])).
% 1.99/1.22  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.22  tff(c_203, plain, (![E_76, C_77, B_78, A_79]: (E_76=C_77 | E_76=B_78 | E_76=A_79 | ~r2_hidden(E_76, k1_enumset1(A_79, B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.22  tff(c_241, plain, (![E_83, B_84, A_85]: (E_83=B_84 | E_83=A_85 | E_83=A_85 | ~r2_hidden(E_83, k2_tarski(A_85, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_203])).
% 1.99/1.22  tff(c_265, plain, (![E_86, A_87]: (E_86=A_87 | E_86=A_87 | E_86=A_87 | ~r2_hidden(E_86, k1_tarski(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_241])).
% 1.99/1.22  tff(c_272, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_133, c_265])).
% 1.99/1.22  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_272])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 52
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 0
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 5
% 1.99/1.22  #Demod        : 9
% 1.99/1.22  #Tautology    : 23
% 1.99/1.22  #SimpNegUnit  : 1
% 1.99/1.22  #BackRed      : 0
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 1.99/1.22  Preprocessing        : 0.29
% 1.99/1.22  Parsing              : 0.15
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.18
% 1.99/1.22  Inferencing          : 0.07
% 1.99/1.22  Reduction            : 0.05
% 1.99/1.22  Demodulation         : 0.04
% 1.99/1.22  BG Simplification    : 0.02
% 1.99/1.22  Subsumption          : 0.03
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.22  Cooper               : 0.00
% 1.99/1.22  Total                : 0.50
% 1.99/1.22  Index Insertion      : 0.00
% 1.99/1.22  Index Deletion       : 0.00
% 1.99/1.22  Index Matching       : 0.00
% 1.99/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
