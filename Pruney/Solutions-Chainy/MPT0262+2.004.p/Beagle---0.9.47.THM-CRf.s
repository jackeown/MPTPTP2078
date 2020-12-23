%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   29 (  46 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  88 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_26,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [D_23,B_24,A_25] :
      ( D_23 = B_24
      | D_23 = A_25
      | ~ r2_hidden(D_23,k2_tarski(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [A_35,B_36,B_37] :
      ( '#skF_1'(k2_tarski(A_35,B_36),B_37) = B_36
      | '#skF_1'(k2_tarski(A_35,B_36),B_37) = A_35
      | r1_xboole_0(k2_tarski(A_35,B_36),B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_67,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_26])).

tff(c_68,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_30,c_72])).

tff(c_80,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_320,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_4])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_28,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  %$ r2_hidden > r1_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.02/1.24  
% 2.02/1.24  %Foreground sorts:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Background operators:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Foreground operators:
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.24  
% 2.02/1.25  tff(f_63, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.02/1.25  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.02/1.25  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.02/1.25  tff(c_26, plain, (~r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.25  tff(c_28, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.25  tff(c_30, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.25  tff(c_36, plain, (![D_23, B_24, A_25]: (D_23=B_24 | D_23=A_25 | ~r2_hidden(D_23, k2_tarski(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_60, plain, (![A_35, B_36, B_37]: ('#skF_1'(k2_tarski(A_35, B_36), B_37)=B_36 | '#skF_1'(k2_tarski(A_35, B_36), B_37)=A_35 | r1_xboole_0(k2_tarski(A_35, B_36), B_37))), inference(resolution, [status(thm)], [c_6, c_36])).
% 2.02/1.25  tff(c_67, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_6' | '#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_26])).
% 2.02/1.25  tff(c_68, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_67])).
% 2.02/1.25  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.25  tff(c_72, plain, (r2_hidden('#skF_4', '#skF_5') | r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_68, c_4])).
% 2.02/1.25  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_30, c_72])).
% 2.02/1.25  tff(c_80, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_67])).
% 2.02/1.25  tff(c_320, plain, (r2_hidden('#skF_6', '#skF_5') | r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_80, c_4])).
% 2.02/1.25  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_28, c_320])).
% 2.02/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 48
% 2.02/1.25  #Fact    : 2
% 2.02/1.25  #Define  : 0
% 2.02/1.25  #Split   : 1
% 2.02/1.25  #Chain   : 0
% 2.02/1.25  #Close   : 0
% 2.02/1.25  
% 2.02/1.25  Ordering : KBO
% 2.02/1.25  
% 2.02/1.25  Simplification rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Subsume      : 4
% 2.02/1.25  #Demod        : 0
% 2.02/1.25  #Tautology    : 8
% 2.02/1.25  #SimpNegUnit  : 2
% 2.02/1.25  #BackRed      : 0
% 2.02/1.25  
% 2.02/1.25  #Partial instantiations: 112
% 2.02/1.25  #Strategies tried      : 1
% 2.02/1.25  
% 2.02/1.25  Timing (in seconds)
% 2.02/1.25  ----------------------
% 2.02/1.25  Preprocessing        : 0.27
% 2.02/1.25  Parsing              : 0.14
% 2.02/1.25  CNF conversion       : 0.02
% 2.02/1.25  Main loop            : 0.21
% 2.02/1.26  Inferencing          : 0.11
% 2.02/1.26  Reduction            : 0.04
% 2.02/1.26  Demodulation         : 0.03
% 2.02/1.26  BG Simplification    : 0.02
% 2.02/1.26  Subsumption          : 0.03
% 2.02/1.26  Abstraction          : 0.01
% 2.02/1.26  MUC search           : 0.00
% 2.02/1.26  Cooper               : 0.00
% 2.02/1.26  Total                : 0.50
% 2.02/1.26  Index Insertion      : 0.00
% 2.02/1.26  Index Deletion       : 0.00
% 2.02/1.26  Index Matching       : 0.00
% 2.02/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
