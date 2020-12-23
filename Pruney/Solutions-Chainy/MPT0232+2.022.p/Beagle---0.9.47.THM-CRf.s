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
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   42 (  82 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 137 expanded)
%              Number of equality atoms :   24 (  81 expanded)
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

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

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

tff(c_288,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_165,c_269])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [B_30,A_29] : r2_hidden(B_30,k2_tarski(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_128,plain,(
    ! [B_49,B_50,A_51] :
      ( r2_hidden(B_49,B_50)
      | ~ r1_tarski(k2_tarski(A_51,B_49),B_50) ) ),
    inference(resolution,[status(thm)],[c_65,c_90])).

tff(c_141,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_128])).

tff(c_289,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_141,c_269])).

tff(c_304,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_289])).

tff(c_38,plain,(
    k2_tarski('#skF_4','#skF_5') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_298,plain,(
    k2_tarski('#skF_4','#skF_5') != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_38])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_304,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.47  
% 2.34/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.47  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.34/1.47  
% 2.34/1.47  %Foreground sorts:
% 2.34/1.47  
% 2.34/1.47  
% 2.34/1.47  %Background operators:
% 2.34/1.47  
% 2.34/1.47  
% 2.34/1.47  %Foreground operators:
% 2.34/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.34/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.34/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.47  
% 2.34/1.48  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.48  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.34/1.48  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.48  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.34/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.34/1.48  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.48  tff(c_40, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.34/1.48  tff(c_53, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.48  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.34/1.48  tff(c_59, plain, (![A_29, B_30]: (r2_hidden(A_29, k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 2.34/1.48  tff(c_90, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.48  tff(c_152, plain, (![A_53, B_54, B_55]: (r2_hidden(A_53, B_54) | ~r1_tarski(k2_tarski(A_53, B_55), B_54))), inference(resolution, [status(thm)], [c_59, c_90])).
% 2.34/1.48  tff(c_165, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_152])).
% 2.34/1.48  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.48  tff(c_196, plain, (![E_65, C_66, B_67, A_68]: (E_65=C_66 | E_65=B_67 | E_65=A_68 | ~r2_hidden(E_65, k1_enumset1(A_68, B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.34/1.48  tff(c_244, plain, (![E_76, B_77, A_78]: (E_76=B_77 | E_76=A_78 | E_76=A_78 | ~r2_hidden(E_76, k2_tarski(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_196])).
% 2.34/1.48  tff(c_269, plain, (![E_83, A_84]: (E_83=A_84 | E_83=A_84 | E_83=A_84 | ~r2_hidden(E_83, k1_tarski(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_244])).
% 2.34/1.48  tff(c_288, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_165, c_269])).
% 2.34/1.48  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.34/1.48  tff(c_65, plain, (![B_30, A_29]: (r2_hidden(B_30, k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 2.34/1.48  tff(c_128, plain, (![B_49, B_50, A_51]: (r2_hidden(B_49, B_50) | ~r1_tarski(k2_tarski(A_51, B_49), B_50))), inference(resolution, [status(thm)], [c_65, c_90])).
% 2.34/1.48  tff(c_141, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_128])).
% 2.34/1.48  tff(c_289, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_141, c_269])).
% 2.34/1.48  tff(c_304, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_289])).
% 2.34/1.48  tff(c_38, plain, (k2_tarski('#skF_4', '#skF_5')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.34/1.48  tff(c_298, plain, (k2_tarski('#skF_4', '#skF_5')!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_38])).
% 2.34/1.48  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_304, c_298])).
% 2.34/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.48  
% 2.34/1.48  Inference rules
% 2.34/1.48  ----------------------
% 2.34/1.48  #Ref     : 0
% 2.34/1.48  #Sup     : 58
% 2.34/1.48  #Fact    : 0
% 2.34/1.48  #Define  : 0
% 2.34/1.48  #Split   : 0
% 2.34/1.48  #Chain   : 0
% 2.34/1.48  #Close   : 0
% 2.34/1.48  
% 2.34/1.48  Ordering : KBO
% 2.34/1.48  
% 2.34/1.48  Simplification rules
% 2.34/1.48  ----------------------
% 2.34/1.48  #Subsume      : 6
% 2.34/1.48  #Demod        : 22
% 2.34/1.48  #Tautology    : 29
% 2.34/1.48  #SimpNegUnit  : 0
% 2.34/1.48  #BackRed      : 6
% 2.34/1.48  
% 2.34/1.48  #Partial instantiations: 0
% 2.34/1.48  #Strategies tried      : 1
% 2.34/1.48  
% 2.34/1.48  Timing (in seconds)
% 2.34/1.48  ----------------------
% 2.34/1.49  Preprocessing        : 0.42
% 2.34/1.49  Parsing              : 0.19
% 2.34/1.49  CNF conversion       : 0.04
% 2.34/1.49  Main loop            : 0.24
% 2.34/1.49  Inferencing          : 0.09
% 2.34/1.49  Reduction            : 0.07
% 2.34/1.49  Demodulation         : 0.05
% 2.34/1.49  BG Simplification    : 0.03
% 2.34/1.49  Subsumption          : 0.05
% 2.34/1.49  Abstraction          : 0.01
% 2.34/1.49  MUC search           : 0.00
% 2.34/1.49  Cooper               : 0.00
% 2.34/1.49  Total                : 0.69
% 2.34/1.49  Index Insertion      : 0.00
% 2.34/1.49  Index Deletion       : 0.00
% 2.34/1.49  Index Matching       : 0.00
% 2.34/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
