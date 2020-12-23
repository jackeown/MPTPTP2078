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
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 43.14s
% Output     : CNFRefutation 43.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  62 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 ( 112 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_3'(A_38,B_39),k3_xboole_0(A_38,B_39))
      | r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_3'(A_40,B_41),A_40)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_74,c_6])).

tff(c_24,plain,(
    ! [D_17,B_13,A_12] :
      ( D_17 = B_13
      | D_17 = A_12
      | ~ r2_hidden(D_17,k2_tarski(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149478,plain,(
    ! [A_32064,B_32065,B_32066] :
      ( '#skF_3'(k2_tarski(A_32064,B_32065),B_32066) = B_32065
      | '#skF_3'(k2_tarski(A_32064,B_32065),B_32066) = A_32064
      | r1_xboole_0(k2_tarski(A_32064,B_32065),B_32066) ) ),
    inference(resolution,[status(thm)],[c_87,c_24])).

tff(c_150174,plain,
    ( '#skF_3'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | '#skF_3'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_149478,c_44])).

tff(c_150175,plain,(
    '#skF_3'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_150174])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_3'(A_38,B_39),B_39)
      | r1_xboole_0(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_150179,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_150175,c_85])).

tff(c_150264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_48,c_150179])).

tff(c_150265,plain,(
    '#skF_3'(k2_tarski('#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_150174])).

tff(c_150270,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | r1_xboole_0(k2_tarski('#skF_6','#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_150265,c_85])).

tff(c_150355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_46,c_150270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.14/32.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.14/32.97  
% 43.14/32.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.14/32.97  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_8
% 43.14/32.97  
% 43.14/32.97  %Foreground sorts:
% 43.14/32.97  
% 43.14/32.97  
% 43.14/32.97  %Background operators:
% 43.14/32.97  
% 43.14/32.97  
% 43.14/32.97  %Foreground operators:
% 43.14/32.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 43.14/32.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.14/32.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.14/32.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 43.14/32.97  tff('#skF_7', type, '#skF_7': $i).
% 43.14/32.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 43.14/32.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.14/32.97  tff('#skF_6', type, '#skF_6': $i).
% 43.14/32.97  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 43.14/32.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 43.14/32.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 43.14/32.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 43.14/32.97  tff('#skF_8', type, '#skF_8': $i).
% 43.14/32.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.14/32.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.14/32.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.14/32.97  
% 43.14/32.98  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 43.14/32.98  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 43.14/32.98  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 43.14/32.98  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 43.14/32.98  tff(c_44, plain, (~r1_xboole_0(k2_tarski('#skF_6', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 43.14/32.98  tff(c_46, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 43.14/32.98  tff(c_48, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 43.14/32.98  tff(c_74, plain, (![A_38, B_39]: (r2_hidden('#skF_3'(A_38, B_39), k3_xboole_0(A_38, B_39)) | r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 43.14/32.98  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 43.14/32.98  tff(c_87, plain, (![A_40, B_41]: (r2_hidden('#skF_3'(A_40, B_41), A_40) | r1_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_74, c_6])).
% 43.14/32.98  tff(c_24, plain, (![D_17, B_13, A_12]: (D_17=B_13 | D_17=A_12 | ~r2_hidden(D_17, k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 43.14/32.98  tff(c_149478, plain, (![A_32064, B_32065, B_32066]: ('#skF_3'(k2_tarski(A_32064, B_32065), B_32066)=B_32065 | '#skF_3'(k2_tarski(A_32064, B_32065), B_32066)=A_32064 | r1_xboole_0(k2_tarski(A_32064, B_32065), B_32066))), inference(resolution, [status(thm)], [c_87, c_24])).
% 43.14/32.98  tff(c_150174, plain, ('#skF_3'(k2_tarski('#skF_6', '#skF_8'), '#skF_7')='#skF_8' | '#skF_3'(k2_tarski('#skF_6', '#skF_8'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_149478, c_44])).
% 43.14/32.98  tff(c_150175, plain, ('#skF_3'(k2_tarski('#skF_6', '#skF_8'), '#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_150174])).
% 43.14/32.98  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 43.14/32.98  tff(c_85, plain, (![A_38, B_39]: (r2_hidden('#skF_3'(A_38, B_39), B_39) | r1_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_74, c_4])).
% 43.14/32.98  tff(c_150179, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k2_tarski('#skF_6', '#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_150175, c_85])).
% 43.14/32.98  tff(c_150264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_48, c_150179])).
% 43.14/32.98  tff(c_150265, plain, ('#skF_3'(k2_tarski('#skF_6', '#skF_8'), '#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_150174])).
% 43.14/32.98  tff(c_150270, plain, (r2_hidden('#skF_8', '#skF_7') | r1_xboole_0(k2_tarski('#skF_6', '#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_150265, c_85])).
% 43.14/32.98  tff(c_150355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_46, c_150270])).
% 43.14/32.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.14/32.98  
% 43.14/32.98  Inference rules
% 43.14/32.98  ----------------------
% 43.14/32.98  #Ref     : 0
% 43.14/32.98  #Sup     : 36130
% 43.14/32.98  #Fact    : 238
% 43.14/32.98  #Define  : 0
% 43.14/32.98  #Split   : 4
% 43.14/32.98  #Chain   : 0
% 43.14/32.98  #Close   : 0
% 43.14/32.98  
% 43.14/32.98  Ordering : KBO
% 43.14/32.98  
% 43.14/32.98  Simplification rules
% 43.14/32.98  ----------------------
% 43.14/32.98  #Subsume      : 13565
% 43.14/32.98  #Demod        : 488
% 43.14/32.98  #Tautology    : 5540
% 43.14/32.98  #SimpNegUnit  : 258
% 43.14/32.98  #BackRed      : 0
% 43.14/32.98  
% 43.14/32.98  #Partial instantiations: 15807
% 43.14/32.98  #Strategies tried      : 1
% 43.14/32.98  
% 43.14/32.98  Timing (in seconds)
% 43.14/32.98  ----------------------
% 43.14/32.99  Preprocessing        : 0.29
% 43.14/32.99  Parsing              : 0.15
% 43.14/32.99  CNF conversion       : 0.02
% 43.14/32.99  Main loop            : 31.93
% 43.14/32.99  Inferencing          : 4.85
% 43.14/32.99  Reduction            : 2.93
% 43.14/32.99  Demodulation         : 1.89
% 43.14/32.99  BG Simplification    : 0.62
% 43.14/32.99  Subsumption          : 22.18
% 43.14/32.99  Abstraction          : 1.08
% 43.14/32.99  MUC search           : 0.00
% 43.14/32.99  Cooper               : 0.00
% 43.14/32.99  Total                : 32.25
% 43.14/32.99  Index Insertion      : 0.00
% 43.14/32.99  Index Deletion       : 0.00
% 43.14/32.99  Index Matching       : 0.00
% 43.14/32.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
