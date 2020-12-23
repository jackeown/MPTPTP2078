%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  65 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_72,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_70,plain,(
    '#skF_6' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ! [D_25,B_21] : r2_hidden(D_25,k2_tarski(D_25,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_102,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_106,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) = k2_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_102])).

tff(c_199,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(A_75,C_76)
      | ~ r2_hidden(A_75,B_77)
      | r2_hidden(A_75,k5_xboole_0(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_9,B_10] : r1_xboole_0(k3_xboole_0(A_9,B_10),k5_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,B_61)
      | ~ r2_hidden(C_62,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [C_62,A_9,B_10] :
      ( ~ r2_hidden(C_62,k5_xboole_0(A_9,B_10))
      | ~ r2_hidden(C_62,k3_xboole_0(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_20,c_139])).

tff(c_226,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r2_hidden(A_81,k3_xboole_0(B_82,C_83))
      | r2_hidden(A_81,C_83)
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_199,c_142])).

tff(c_288,plain,(
    ! [A_93] :
      ( ~ r2_hidden(A_93,k2_tarski('#skF_6','#skF_7'))
      | r2_hidden(A_93,k2_tarski('#skF_8','#skF_9'))
      | ~ r2_hidden(A_93,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_226])).

tff(c_300,plain,
    ( r2_hidden('#skF_6',k2_tarski('#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_6',k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_288])).

tff(c_308,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_300])).

tff(c_48,plain,(
    ! [D_25,B_21,A_20] :
      ( D_25 = B_21
      | D_25 = A_20
      | ~ r2_hidden(D_25,k2_tarski(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_327,plain,
    ( '#skF_6' = '#skF_9'
    | '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_308,c_48])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 2.43/1.38  
% 2.43/1.38  %Foreground sorts:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Background operators:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Foreground operators:
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.43/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.43/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.43/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.43/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.43/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.43/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.38  
% 2.43/1.39  tff(f_94, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.43/1.39  tff(f_80, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.43/1.39  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.43/1.39  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.43/1.39  tff(f_52, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.43/1.39  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.43/1.39  tff(c_72, plain, ('#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.43/1.39  tff(c_70, plain, ('#skF_6'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.43/1.39  tff(c_52, plain, (![D_25, B_21]: (r2_hidden(D_25, k2_tarski(D_25, B_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.39  tff(c_74, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.43/1.39  tff(c_102, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.39  tff(c_106, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))=k2_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_102])).
% 2.43/1.39  tff(c_199, plain, (![A_75, C_76, B_77]: (r2_hidden(A_75, C_76) | ~r2_hidden(A_75, B_77) | r2_hidden(A_75, k5_xboole_0(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.43/1.39  tff(c_20, plain, (![A_9, B_10]: (r1_xboole_0(k3_xboole_0(A_9, B_10), k5_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.43/1.39  tff(c_139, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, B_61) | ~r2_hidden(C_62, A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.39  tff(c_142, plain, (![C_62, A_9, B_10]: (~r2_hidden(C_62, k5_xboole_0(A_9, B_10)) | ~r2_hidden(C_62, k3_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_20, c_139])).
% 2.43/1.39  tff(c_226, plain, (![A_81, B_82, C_83]: (~r2_hidden(A_81, k3_xboole_0(B_82, C_83)) | r2_hidden(A_81, C_83) | ~r2_hidden(A_81, B_82))), inference(resolution, [status(thm)], [c_199, c_142])).
% 2.43/1.39  tff(c_288, plain, (![A_93]: (~r2_hidden(A_93, k2_tarski('#skF_6', '#skF_7')) | r2_hidden(A_93, k2_tarski('#skF_8', '#skF_9')) | ~r2_hidden(A_93, k2_tarski('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_226])).
% 2.43/1.39  tff(c_300, plain, (r2_hidden('#skF_6', k2_tarski('#skF_8', '#skF_9')) | ~r2_hidden('#skF_6', k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_288])).
% 2.43/1.39  tff(c_308, plain, (r2_hidden('#skF_6', k2_tarski('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_300])).
% 2.43/1.39  tff(c_48, plain, (![D_25, B_21, A_20]: (D_25=B_21 | D_25=A_20 | ~r2_hidden(D_25, k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.39  tff(c_327, plain, ('#skF_6'='#skF_9' | '#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_308, c_48])).
% 2.43/1.39  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_327])).
% 2.43/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.39  
% 2.43/1.39  Inference rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Ref     : 0
% 2.43/1.39  #Sup     : 54
% 2.43/1.39  #Fact    : 0
% 2.43/1.39  #Define  : 0
% 2.43/1.39  #Split   : 1
% 2.43/1.39  #Chain   : 0
% 2.43/1.39  #Close   : 0
% 2.43/1.39  
% 2.43/1.39  Ordering : KBO
% 2.43/1.39  
% 2.43/1.39  Simplification rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Subsume      : 2
% 2.43/1.39  #Demod        : 16
% 2.43/1.39  #Tautology    : 24
% 2.43/1.39  #SimpNegUnit  : 1
% 2.43/1.39  #BackRed      : 6
% 2.43/1.39  
% 2.43/1.39  #Partial instantiations: 0
% 2.43/1.39  #Strategies tried      : 1
% 2.43/1.39  
% 2.43/1.39  Timing (in seconds)
% 2.43/1.39  ----------------------
% 2.43/1.40  Preprocessing        : 0.32
% 2.43/1.40  Parsing              : 0.15
% 2.43/1.40  CNF conversion       : 0.03
% 2.43/1.40  Main loop            : 0.31
% 2.43/1.40  Inferencing          : 0.09
% 2.43/1.40  Reduction            : 0.10
% 2.43/1.40  Demodulation         : 0.08
% 2.43/1.40  BG Simplification    : 0.02
% 2.43/1.40  Subsumption          : 0.07
% 2.43/1.40  Abstraction          : 0.01
% 2.43/1.40  MUC search           : 0.00
% 2.43/1.40  Cooper               : 0.00
% 2.43/1.40  Total                : 0.65
% 2.43/1.40  Index Insertion      : 0.00
% 2.43/1.40  Index Deletion       : 0.00
% 2.43/1.40  Index Matching       : 0.00
% 2.43/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
