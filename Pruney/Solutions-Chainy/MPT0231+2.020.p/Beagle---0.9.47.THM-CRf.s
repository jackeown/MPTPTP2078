%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  53 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

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

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_38,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_29,B_30] : r2_hidden(A_29,k2_tarski(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_90,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [A_53,B_54,B_55] :
      ( r2_hidden(A_53,B_54)
      | ~ r1_tarski(k2_tarski(A_53,B_55),B_54) ) ),
    inference(resolution,[status(thm)],[c_59,c_90])).

tff(c_165,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_152])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_196,plain,(
    ! [E_65,C_66,B_67,A_68] :
      ( E_65 = C_66
      | E_65 = B_67
      | E_65 = A_68
      | ~ r2_hidden(E_65,k1_enumset1(A_68,B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_244,plain,(
    ! [E_76,B_77,A_78] :
      ( E_76 = B_77
      | E_76 = A_78
      | E_76 = A_78
      | ~ r2_hidden(E_76,k2_tarski(A_78,B_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_196])).

tff(c_269,plain,(
    ! [E_83,A_84] :
      ( E_83 = A_84
      | E_83 = A_84
      | E_83 = A_84
      | ~ r2_hidden(E_83,k1_tarski(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_244])).

tff(c_276,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_165,c_269])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_38,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:05:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.25  
% 2.05/1.25  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.05/1.25  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.05/1.25  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.05/1.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.25  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.25  tff(c_38, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.25  tff(c_40, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.25  tff(c_53, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.25  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.25  tff(c_59, plain, (![A_29, B_30]: (r2_hidden(A_29, k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 2.05/1.25  tff(c_90, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.25  tff(c_152, plain, (![A_53, B_54, B_55]: (r2_hidden(A_53, B_54) | ~r1_tarski(k2_tarski(A_53, B_55), B_54))), inference(resolution, [status(thm)], [c_59, c_90])).
% 2.05/1.25  tff(c_165, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_152])).
% 2.05/1.25  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.25  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.25  tff(c_196, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.25  tff(c_244, plain, (![E_76, B_77, A_78]: (E_76=B_77 | E_76=A_78 | E_76=A_78 | ~r2_hidden(E_76, k2_tarski(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_196])).
% 2.05/1.25  tff(c_269, plain, (![E_83, A_84]: (E_83=A_84 | E_83=A_84 | E_83=A_84 | ~r2_hidden(E_83, k1_tarski(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_244])).
% 2.05/1.25  tff(c_276, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_165, c_269])).
% 2.05/1.25  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_38, c_276])).
% 2.05/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  Inference rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Ref     : 0
% 2.05/1.25  #Sup     : 54
% 2.05/1.25  #Fact    : 0
% 2.05/1.25  #Define  : 0
% 2.05/1.25  #Split   : 0
% 2.05/1.25  #Chain   : 0
% 2.05/1.25  #Close   : 0
% 2.05/1.25  
% 2.05/1.25  Ordering : KBO
% 2.05/1.25  
% 2.05/1.25  Simplification rules
% 2.05/1.25  ----------------------
% 2.05/1.25  #Subsume      : 5
% 2.05/1.25  #Demod        : 10
% 2.05/1.25  #Tautology    : 22
% 2.05/1.25  #SimpNegUnit  : 1
% 2.05/1.25  #BackRed      : 0
% 2.05/1.25  
% 2.05/1.25  #Partial instantiations: 0
% 2.05/1.25  #Strategies tried      : 1
% 2.05/1.25  
% 2.05/1.25  Timing (in seconds)
% 2.05/1.25  ----------------------
% 2.05/1.26  Preprocessing        : 0.29
% 2.05/1.26  Parsing              : 0.14
% 2.05/1.26  CNF conversion       : 0.02
% 2.05/1.26  Main loop            : 0.19
% 2.05/1.26  Inferencing          : 0.07
% 2.05/1.26  Reduction            : 0.06
% 2.05/1.26  Demodulation         : 0.04
% 2.05/1.26  BG Simplification    : 0.02
% 2.05/1.26  Subsumption          : 0.04
% 2.05/1.26  Abstraction          : 0.01
% 2.05/1.26  MUC search           : 0.00
% 2.05/1.26  Cooper               : 0.00
% 2.05/1.26  Total                : 0.51
% 2.05/1.26  Index Insertion      : 0.00
% 2.05/1.26  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
