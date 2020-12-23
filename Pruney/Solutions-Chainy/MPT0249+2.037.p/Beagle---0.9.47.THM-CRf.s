%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   47 (  87 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 140 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_41])).

tff(c_94,plain,(
    ! [B_30,A_31] :
      ( k1_tarski(B_30) = A_31
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_107,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_97])).

tff(c_76,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_93,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_93])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_118,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_121,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_32])).

tff(c_8,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_188,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,k2_xboole_0(B_39,C_40))
      | ~ r1_tarski(k4_xboole_0(A_38,B_39),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_38,B_39] : r1_tarski(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_200,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_196])).

tff(c_209,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_200])).

tff(c_147,plain,(
    ! [B_32,A_33] :
      ( k1_tarski(B_32) = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,(
    ! [A_33] :
      ( k1_tarski('#skF_1') = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_147])).

tff(c_158,plain,(
    ! [A_33] :
      ( A_33 = '#skF_2'
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_150])).

tff(c_217,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_209,c_158])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_30,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:56:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.16  
% 1.69/1.17  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.69/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.69/1.17  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.17  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.69/1.17  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.69/1.17  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.69/1.17  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.17  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.17  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.17  tff(c_32, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.17  tff(c_41, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.17  tff(c_44, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_41])).
% 1.69/1.17  tff(c_94, plain, (![B_30, A_31]: (k1_tarski(B_30)=A_31 | k1_xboole_0=A_31 | ~r1_tarski(A_31, k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.69/1.17  tff(c_97, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_44, c_94])).
% 1.69/1.17  tff(c_107, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28, c_97])).
% 1.69/1.17  tff(c_76, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.17  tff(c_85, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_76])).
% 1.69/1.17  tff(c_93, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_85])).
% 1.69/1.17  tff(c_112, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_93])).
% 1.69/1.17  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_112])).
% 1.69/1.17  tff(c_118, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_85])).
% 1.69/1.17  tff(c_121, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_32])).
% 1.69/1.17  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.17  tff(c_188, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, k2_xboole_0(B_39, C_40)) | ~r1_tarski(k4_xboole_0(A_38, B_39), C_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.17  tff(c_196, plain, (![A_38, B_39]: (r1_tarski(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39))))), inference(resolution, [status(thm)], [c_6, c_188])).
% 1.69/1.17  tff(c_200, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_196])).
% 1.69/1.17  tff(c_209, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_200])).
% 1.69/1.17  tff(c_147, plain, (![B_32, A_33]: (k1_tarski(B_32)=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.69/1.17  tff(c_150, plain, (![A_33]: (k1_tarski('#skF_1')=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_147])).
% 1.69/1.17  tff(c_158, plain, (![A_33]: (A_33='#skF_2' | k1_xboole_0=A_33 | ~r1_tarski(A_33, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_150])).
% 1.69/1.17  tff(c_217, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_209, c_158])).
% 1.69/1.17  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_30, c_217])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 40
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 1
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 1
% 1.69/1.17  #Demod        : 17
% 1.69/1.17  #Tautology    : 27
% 1.69/1.17  #SimpNegUnit  : 6
% 1.69/1.17  #BackRed      : 5
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.95/1.17  Preprocessing        : 0.29
% 1.95/1.17  Parsing              : 0.15
% 1.95/1.17  CNF conversion       : 0.02
% 1.95/1.17  Main loop            : 0.15
% 1.95/1.17  Inferencing          : 0.05
% 1.95/1.17  Reduction            : 0.05
% 1.95/1.17  Demodulation         : 0.04
% 1.95/1.17  BG Simplification    : 0.01
% 1.95/1.17  Subsumption          : 0.03
% 1.95/1.17  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.47
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
