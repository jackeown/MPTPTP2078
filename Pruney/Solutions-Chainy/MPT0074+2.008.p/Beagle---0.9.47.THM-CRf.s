%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  67 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_11,B_23] :
      ( r2_hidden('#skF_3'(A_11),B_23)
      | ~ r1_tarski(A_11,B_23)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_3'(A_30),B_31)
      | ~ r1_tarski(A_30,B_31)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_18,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_47,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_6')
      | ~ r2_hidden(C_28,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_47])).

tff(c_104,plain,(
    ! [A_35] :
      ( ~ r2_hidden('#skF_3'(A_35),'#skF_6')
      | ~ r1_tarski(A_35,'#skF_5')
      | k1_xboole_0 = A_35 ) ),
    inference(resolution,[status(thm)],[c_73,c_50])).

tff(c_139,plain,(
    ! [A_40] :
      ( ~ r1_tarski(A_40,'#skF_5')
      | ~ r1_tarski(A_40,'#skF_6')
      | k1_xboole_0 = A_40 ) ),
    inference(resolution,[status(thm)],[c_45,c_104])).

tff(c_146,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.19  
% 1.87/1.20  tff(f_67, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.87/1.20  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.87/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.20  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.87/1.20  tff(c_16, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.20  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.20  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.20  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.20  tff(c_33, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.20  tff(c_45, plain, (![A_11, B_23]: (r2_hidden('#skF_3'(A_11), B_23) | ~r1_tarski(A_11, B_23) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.87/1.20  tff(c_73, plain, (![A_30, B_31]: (r2_hidden('#skF_3'(A_30), B_31) | ~r1_tarski(A_30, B_31) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.87/1.20  tff(c_18, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.20  tff(c_47, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, B_27) | ~r2_hidden(C_28, A_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.20  tff(c_50, plain, (![C_28]: (~r2_hidden(C_28, '#skF_6') | ~r2_hidden(C_28, '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_47])).
% 1.87/1.20  tff(c_104, plain, (![A_35]: (~r2_hidden('#skF_3'(A_35), '#skF_6') | ~r1_tarski(A_35, '#skF_5') | k1_xboole_0=A_35)), inference(resolution, [status(thm)], [c_73, c_50])).
% 1.87/1.20  tff(c_139, plain, (![A_40]: (~r1_tarski(A_40, '#skF_5') | ~r1_tarski(A_40, '#skF_6') | k1_xboole_0=A_40)), inference(resolution, [status(thm)], [c_45, c_104])).
% 1.87/1.20  tff(c_146, plain, (~r1_tarski('#skF_4', '#skF_6') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22, c_139])).
% 1.87/1.20  tff(c_150, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_146])).
% 1.87/1.20  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_150])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 25
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 3
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 3
% 1.87/1.20  #Demod        : 2
% 1.87/1.20  #Tautology    : 1
% 1.87/1.20  #SimpNegUnit  : 1
% 1.87/1.20  #BackRed      : 0
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.21  Preprocessing        : 0.27
% 1.87/1.21  Parsing              : 0.15
% 1.87/1.21  CNF conversion       : 0.02
% 1.87/1.21  Main loop            : 0.16
% 1.87/1.21  Inferencing          : 0.06
% 1.87/1.21  Reduction            : 0.04
% 1.87/1.21  Demodulation         : 0.03
% 1.87/1.21  BG Simplification    : 0.01
% 1.87/1.21  Subsumption          : 0.04
% 1.87/1.21  Abstraction          : 0.01
% 1.87/1.21  MUC search           : 0.00
% 1.87/1.21  Cooper               : 0.00
% 1.87/1.21  Total                : 0.45
% 1.87/1.21  Index Insertion      : 0.00
% 1.87/1.21  Index Deletion       : 0.00
% 1.87/1.21  Index Matching       : 0.00
% 1.87/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
