%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  54 expanded)
%              Number of equality atoms :   22 (  43 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_107,plain,(
    ! [B_15,A_16] :
      ( k1_tarski(B_15) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_83,c_107])).

tff(c_122,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_110])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_25,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_25])).

tff(c_113,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_125,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_113])).

tff(c_152,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_125])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.12  %$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.73/1.12  
% 1.73/1.12  %Foreground sorts:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Background operators:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Foreground operators:
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.12  
% 1.73/1.13  tff(f_48, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.73/1.13  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.73/1.13  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.73/1.13  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.73/1.13  tff(c_16, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.13  tff(c_12, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.13  tff(c_18, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.13  tff(c_29, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.73/1.13  tff(c_71, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_29])).
% 1.73/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.13  tff(c_83, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 1.73/1.13  tff(c_107, plain, (![B_15, A_16]: (k1_tarski(B_15)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.13  tff(c_110, plain, (k1_tarski('#skF_1')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_83, c_107])).
% 1.73/1.13  tff(c_122, plain, (k1_tarski('#skF_1')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_12, c_110])).
% 1.73/1.13  tff(c_14, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.13  tff(c_25, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.13  tff(c_28, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_25])).
% 1.73/1.13  tff(c_113, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_107])).
% 1.73/1.13  tff(c_125, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14, c_113])).
% 1.73/1.13  tff(c_152, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_125])).
% 1.73/1.13  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_152])).
% 1.73/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  Inference rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Ref     : 0
% 1.73/1.13  #Sup     : 34
% 1.73/1.13  #Fact    : 0
% 1.73/1.13  #Define  : 0
% 1.73/1.13  #Split   : 0
% 1.73/1.13  #Chain   : 0
% 1.73/1.13  #Close   : 0
% 1.73/1.13  
% 1.73/1.13  Ordering : KBO
% 1.73/1.13  
% 1.73/1.13  Simplification rules
% 1.73/1.13  ----------------------
% 1.73/1.13  #Subsume      : 0
% 1.73/1.13  #Demod        : 15
% 1.73/1.13  #Tautology    : 23
% 1.73/1.13  #SimpNegUnit  : 3
% 1.73/1.13  #BackRed      : 5
% 1.73/1.13  
% 1.73/1.13  #Partial instantiations: 0
% 1.73/1.13  #Strategies tried      : 1
% 1.73/1.13  
% 1.73/1.13  Timing (in seconds)
% 1.73/1.13  ----------------------
% 1.73/1.14  Preprocessing        : 0.26
% 1.73/1.14  Parsing              : 0.14
% 1.73/1.14  CNF conversion       : 0.02
% 1.73/1.14  Main loop            : 0.12
% 1.73/1.14  Inferencing          : 0.04
% 1.73/1.14  Reduction            : 0.05
% 1.73/1.14  Demodulation         : 0.04
% 1.73/1.14  BG Simplification    : 0.01
% 1.73/1.14  Subsumption          : 0.02
% 1.73/1.14  Abstraction          : 0.01
% 1.73/1.14  MUC search           : 0.00
% 1.73/1.14  Cooper               : 0.00
% 1.73/1.14  Total                : 0.40
% 1.73/1.14  Index Insertion      : 0.00
% 1.73/1.14  Index Deletion       : 0.00
% 1.73/1.14  Index Matching       : 0.00
% 1.73/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
