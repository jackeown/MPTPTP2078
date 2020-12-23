%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  69 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | r2_hidden(D_39,k2_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,'#skF_6')
      | r2_hidden(D_39,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_133,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_51,k1_tarski('#skF_4')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_122,c_133])).

tff(c_164,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_176,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_179,plain,
    ( k1_tarski('#skF_4') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_164,c_176])).

tff(c_192,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_179])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_66])).

tff(c_186,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_69,c_176])).

tff(c_197,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_186])).

tff(c_235,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_197])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.26  % Computer   : n009.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 12:39:26 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.18  
% 1.92/1.19  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.92/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.19  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.92/1.19  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.92/1.19  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.19  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.92/1.19  tff(c_44, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.92/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.19  tff(c_50, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.92/1.19  tff(c_116, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | r2_hidden(D_39, k2_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.19  tff(c_122, plain, (![D_39]: (~r2_hidden(D_39, '#skF_6') | r2_hidden(D_39, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_116])).
% 1.92/1.19  tff(c_133, plain, (![A_49, B_50]: (~r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.19  tff(c_159, plain, (![A_51]: (r1_tarski(A_51, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_51, k1_tarski('#skF_4')), '#skF_6'))), inference(resolution, [status(thm)], [c_122, c_133])).
% 1.92/1.19  tff(c_164, plain, (r1_tarski('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_159])).
% 1.92/1.19  tff(c_176, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.19  tff(c_179, plain, (k1_tarski('#skF_4')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_164, c_176])).
% 1.92/1.19  tff(c_192, plain, (k1_tarski('#skF_4')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_44, c_179])).
% 1.92/1.19  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.92/1.19  tff(c_66, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.19  tff(c_69, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_66])).
% 1.92/1.19  tff(c_186, plain, (k1_tarski('#skF_4')='#skF_5' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_69, c_176])).
% 1.92/1.19  tff(c_197, plain, (k1_tarski('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_186])).
% 1.92/1.19  tff(c_235, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_197])).
% 1.92/1.19  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_235])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 41
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 0
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 2
% 1.92/1.19  #Demod        : 12
% 1.92/1.19  #Tautology    : 22
% 1.92/1.19  #SimpNegUnit  : 3
% 1.92/1.19  #BackRed      : 6
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.33
% 1.92/1.19  Parsing              : 0.17
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.16
% 1.92/1.19  Inferencing          : 0.06
% 1.92/1.19  Reduction            : 0.05
% 1.92/1.19  Demodulation         : 0.04
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.03
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.51
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
