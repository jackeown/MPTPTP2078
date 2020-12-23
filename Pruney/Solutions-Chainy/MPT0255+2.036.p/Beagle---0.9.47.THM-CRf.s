%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  99 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 119 expanded)
%              Number of equality atoms :   14 (  44 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_62,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_22,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    ! [A_42,B_41] : r1_tarski(A_42,k2_xboole_0(B_41,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_26])).

tff(c_112,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_75])).

tff(c_164,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_112,c_164])).

tff(c_182,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_121,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_26])).

tff(c_166,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_121,c_164])).

tff(c_179,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_166])).

tff(c_206,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_179])).

tff(c_32,plain,(
    ! [D_24,B_20] : r2_hidden(D_24,k2_tarski(D_24,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_216,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_32])).

tff(c_24,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_195,plain,(
    ! [A_16] : r1_xboole_0(A_16,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_24])).

tff(c_313,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,B_66)
      | ~ r2_hidden(C_67,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_317,plain,(
    ! [C_68,A_69] :
      ( ~ r2_hidden(C_68,'#skF_7')
      | ~ r2_hidden(C_68,A_69) ) ),
    inference(resolution,[status(thm)],[c_195,c_313])).

tff(c_336,plain,(
    ! [A_69] : ~ r2_hidden('#skF_5',A_69) ),
    inference(resolution,[status(thm)],[c_216,c_317])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.23/1.31  
% 2.23/1.31  %Foreground sorts:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Background operators:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Foreground operators:
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.23/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.31  
% 2.23/1.32  tff(f_60, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.32  tff(f_83, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.23/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/1.32  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.23/1.32  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.32  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/1.32  tff(f_62, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.32  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.23/1.32  tff(c_22, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.32  tff(c_52, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.32  tff(c_60, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.32  tff(c_26, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.32  tff(c_75, plain, (![A_42, B_41]: (r1_tarski(A_42, k2_xboole_0(B_41, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_26])).
% 2.23/1.32  tff(c_112, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_75])).
% 2.23/1.32  tff(c_164, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.32  tff(c_168, plain, (k1_xboole_0='#skF_7' | ~r1_tarski(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_112, c_164])).
% 2.23/1.32  tff(c_182, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_168])).
% 2.23/1.32  tff(c_121, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_26])).
% 2.23/1.32  tff(c_166, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_121, c_164])).
% 2.23/1.32  tff(c_179, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_166])).
% 2.23/1.32  tff(c_206, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_179])).
% 2.23/1.32  tff(c_32, plain, (![D_24, B_20]: (r2_hidden(D_24, k2_tarski(D_24, B_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.32  tff(c_216, plain, (r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_206, c_32])).
% 2.23/1.32  tff(c_24, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.32  tff(c_195, plain, (![A_16]: (r1_xboole_0(A_16, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_24])).
% 2.23/1.32  tff(c_313, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, B_66) | ~r2_hidden(C_67, A_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.32  tff(c_317, plain, (![C_68, A_69]: (~r2_hidden(C_68, '#skF_7') | ~r2_hidden(C_68, A_69))), inference(resolution, [status(thm)], [c_195, c_313])).
% 2.23/1.32  tff(c_336, plain, (![A_69]: (~r2_hidden('#skF_5', A_69))), inference(resolution, [status(thm)], [c_216, c_317])).
% 2.23/1.32  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_216])).
% 2.23/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  Inference rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Ref     : 0
% 2.23/1.32  #Sup     : 71
% 2.23/1.32  #Fact    : 0
% 2.23/1.32  #Define  : 0
% 2.23/1.32  #Split   : 2
% 2.23/1.32  #Chain   : 0
% 2.23/1.32  #Close   : 0
% 2.23/1.32  
% 2.23/1.32  Ordering : KBO
% 2.23/1.32  
% 2.23/1.32  Simplification rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Subsume      : 1
% 2.23/1.32  #Demod        : 37
% 2.23/1.32  #Tautology    : 53
% 2.23/1.32  #SimpNegUnit  : 1
% 2.23/1.32  #BackRed      : 7
% 2.23/1.32  
% 2.23/1.32  #Partial instantiations: 0
% 2.23/1.32  #Strategies tried      : 1
% 2.23/1.32  
% 2.23/1.32  Timing (in seconds)
% 2.23/1.32  ----------------------
% 2.23/1.32  Preprocessing        : 0.33
% 2.23/1.32  Parsing              : 0.17
% 2.23/1.32  CNF conversion       : 0.02
% 2.23/1.32  Main loop            : 0.23
% 2.23/1.32  Inferencing          : 0.07
% 2.23/1.32  Reduction            : 0.08
% 2.23/1.32  Demodulation         : 0.06
% 2.23/1.32  BG Simplification    : 0.02
% 2.23/1.32  Subsumption          : 0.05
% 2.23/1.32  Abstraction          : 0.01
% 2.23/1.32  MUC search           : 0.00
% 2.23/1.32  Cooper               : 0.00
% 2.23/1.32  Total                : 0.59
% 2.23/1.32  Index Insertion      : 0.00
% 2.23/1.32  Index Deletion       : 0.00
% 2.23/1.32  Index Matching       : 0.00
% 2.23/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
