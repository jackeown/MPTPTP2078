%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   44 (  46 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_78,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_151,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [B_48,A_47] : r2_hidden(B_48,k2_tarski(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_38])).

tff(c_82,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_189,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_201,plain,(
    k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_7')) = k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_189])).

tff(c_32,plain,(
    ! [A_9,C_11,B_10] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(A_9,B_10)
      | r2_hidden(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_698,plain,(
    ! [A_111] :
      ( r2_hidden(A_111,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_111,k2_tarski('#skF_7','#skF_8'))
      | r2_hidden(A_111,k4_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_32])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_721,plain,(
    ! [A_112] :
      ( ~ r2_hidden(A_112,'#skF_9')
      | r2_hidden(A_112,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_112,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_698,c_6])).

tff(c_744,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_160,c_721])).

tff(c_756,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_744])).

tff(c_60,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_762,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_756,c_60])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:12:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.39  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.63/1.39  
% 2.63/1.39  %Foreground sorts:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Background operators:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Foreground operators:
% 2.63/1.39  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.63/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.63/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.63/1.39  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.63/1.39  
% 2.63/1.40  tff(f_83, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.63/1.40  tff(f_72, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.63/1.40  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.63/1.40  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.63/1.40  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.63/1.40  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.63/1.40  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.63/1.40  tff(c_78, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.40  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.40  tff(c_151, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.40  tff(c_38, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.63/1.40  tff(c_160, plain, (![B_48, A_47]: (r2_hidden(B_48, k2_tarski(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_38])).
% 2.63/1.40  tff(c_82, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.63/1.40  tff(c_189, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.40  tff(c_201, plain, (k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_7'))=k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_82, c_189])).
% 2.63/1.40  tff(c_32, plain, (![A_9, C_11, B_10]: (r2_hidden(A_9, C_11) | ~r2_hidden(A_9, B_10) | r2_hidden(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.40  tff(c_698, plain, (![A_111]: (r2_hidden(A_111, k1_tarski('#skF_7')) | ~r2_hidden(A_111, k2_tarski('#skF_7', '#skF_8')) | r2_hidden(A_111, k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_201, c_32])).
% 2.63/1.40  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.40  tff(c_721, plain, (![A_112]: (~r2_hidden(A_112, '#skF_9') | r2_hidden(A_112, k1_tarski('#skF_7')) | ~r2_hidden(A_112, k2_tarski('#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_698, c_6])).
% 2.63/1.40  tff(c_744, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_160, c_721])).
% 2.63/1.40  tff(c_756, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_744])).
% 2.63/1.40  tff(c_60, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.63/1.40  tff(c_762, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_756, c_60])).
% 2.63/1.40  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_762])).
% 2.63/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  Inference rules
% 2.63/1.40  ----------------------
% 2.93/1.40  #Ref     : 0
% 2.93/1.40  #Sup     : 154
% 2.93/1.40  #Fact    : 0
% 2.93/1.40  #Define  : 0
% 2.93/1.40  #Split   : 0
% 2.93/1.40  #Chain   : 0
% 2.93/1.40  #Close   : 0
% 2.93/1.40  
% 2.93/1.40  Ordering : KBO
% 2.93/1.40  
% 2.93/1.40  Simplification rules
% 2.93/1.40  ----------------------
% 2.93/1.40  #Subsume      : 12
% 2.93/1.40  #Demod        : 18
% 2.93/1.40  #Tautology    : 60
% 2.93/1.40  #SimpNegUnit  : 1
% 2.93/1.40  #BackRed      : 0
% 2.93/1.40  
% 2.93/1.40  #Partial instantiations: 0
% 2.93/1.40  #Strategies tried      : 1
% 2.93/1.40  
% 2.93/1.40  Timing (in seconds)
% 2.93/1.40  ----------------------
% 2.93/1.40  Preprocessing        : 0.31
% 2.93/1.40  Parsing              : 0.15
% 2.93/1.40  CNF conversion       : 0.03
% 2.93/1.40  Main loop            : 0.34
% 2.93/1.40  Inferencing          : 0.12
% 2.93/1.40  Reduction            : 0.11
% 2.93/1.40  Demodulation         : 0.09
% 2.93/1.40  BG Simplification    : 0.02
% 2.93/1.40  Subsumption          : 0.07
% 2.93/1.40  Abstraction          : 0.02
% 2.93/1.40  MUC search           : 0.00
% 2.93/1.40  Cooper               : 0.00
% 2.93/1.40  Total                : 0.68
% 2.93/1.40  Index Insertion      : 0.00
% 2.93/1.40  Index Deletion       : 0.00
% 2.93/1.40  Index Matching       : 0.00
% 2.93/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
