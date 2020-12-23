%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 23.49s
% Output     : CNFRefutation 23.49s
% Verified   : 
% Statistics : Number of formulae       :   39 (  75 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 162 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),A_55)
      | r2_hidden('#skF_2'(A_55,B_56,C_57),C_57)
      | k4_xboole_0(A_55,B_56) = C_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56,A_55),A_55)
      | k4_xboole_0(A_55,B_56) = A_55 ) ),
    inference(resolution,[status(thm)],[c_134,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_770,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r2_hidden('#skF_1'(A_105,B_106,C_107),C_107)
      | r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | ~ r2_hidden('#skF_2'(A_105,B_106,C_107),A_105)
      | k4_xboole_0(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1426,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_2'(A_127,B_128,A_127),B_128)
      | ~ r2_hidden('#skF_2'(A_127,B_128,A_127),A_127)
      | k4_xboole_0(A_127,B_128) = A_127 ) ),
    inference(resolution,[status(thm)],[c_12,c_770])).

tff(c_1440,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_2'(A_129,B_130,A_129),B_130)
      | k4_xboole_0(A_129,B_130) = A_129 ) ),
    inference(resolution,[status(thm)],[c_163,c_1426])).

tff(c_22,plain,(
    ! [D_14,B_10,A_9] :
      ( D_14 = B_10
      | D_14 = A_9
      | ~ r2_hidden(D_14,k2_tarski(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69806,plain,(
    ! [A_8113,A_8114,B_8115] :
      ( '#skF_2'(A_8113,k2_tarski(A_8114,B_8115),A_8113) = B_8115
      | '#skF_2'(A_8113,k2_tarski(A_8114,B_8115),A_8113) = A_8114
      | k4_xboole_0(A_8113,k2_tarski(A_8114,B_8115)) = A_8113 ) ),
    inference(resolution,[status(thm)],[c_1440,c_22])).

tff(c_70594,plain,
    ( '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_6'
    | '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_69806,c_44])).

tff(c_70816,plain,(
    '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_70594])).

tff(c_70834,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_70816,c_163])).

tff(c_70847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_48,c_70834])).

tff(c_70848,plain,(
    '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70594])).

tff(c_70867,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_70848,c_163])).

tff(c_70880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_46,c_70867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.49/11.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.34  
% 23.49/11.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.34  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 23.49/11.34  
% 23.49/11.34  %Foreground sorts:
% 23.49/11.34  
% 23.49/11.34  
% 23.49/11.34  %Background operators:
% 23.49/11.34  
% 23.49/11.34  
% 23.49/11.34  %Foreground operators:
% 23.49/11.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.49/11.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.49/11.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.49/11.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.49/11.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 23.49/11.34  tff('#skF_7', type, '#skF_7': $i).
% 23.49/11.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.49/11.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.49/11.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.49/11.34  tff('#skF_5', type, '#skF_5': $i).
% 23.49/11.34  tff('#skF_6', type, '#skF_6': $i).
% 23.49/11.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.49/11.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.49/11.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.49/11.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.49/11.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.49/11.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.49/11.34  
% 23.49/11.35  tff(f_61, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 23.49/11.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 23.49/11.35  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 23.49/11.35  tff(c_44, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.49/11.35  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.49/11.35  tff(c_48, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.49/11.35  tff(c_134, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), A_55) | r2_hidden('#skF_2'(A_55, B_56, C_57), C_57) | k4_xboole_0(A_55, B_56)=C_57)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.49/11.35  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.49/11.35  tff(c_163, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56, A_55), A_55) | k4_xboole_0(A_55, B_56)=A_55)), inference(resolution, [status(thm)], [c_134, c_14])).
% 23.49/11.35  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.49/11.35  tff(c_770, plain, (![A_105, B_106, C_107]: (~r2_hidden('#skF_1'(A_105, B_106, C_107), C_107) | r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | ~r2_hidden('#skF_2'(A_105, B_106, C_107), A_105) | k4_xboole_0(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.49/11.35  tff(c_1426, plain, (![A_127, B_128]: (r2_hidden('#skF_2'(A_127, B_128, A_127), B_128) | ~r2_hidden('#skF_2'(A_127, B_128, A_127), A_127) | k4_xboole_0(A_127, B_128)=A_127)), inference(resolution, [status(thm)], [c_12, c_770])).
% 23.49/11.35  tff(c_1440, plain, (![A_129, B_130]: (r2_hidden('#skF_2'(A_129, B_130, A_129), B_130) | k4_xboole_0(A_129, B_130)=A_129)), inference(resolution, [status(thm)], [c_163, c_1426])).
% 23.49/11.35  tff(c_22, plain, (![D_14, B_10, A_9]: (D_14=B_10 | D_14=A_9 | ~r2_hidden(D_14, k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 23.49/11.35  tff(c_69806, plain, (![A_8113, A_8114, B_8115]: ('#skF_2'(A_8113, k2_tarski(A_8114, B_8115), A_8113)=B_8115 | '#skF_2'(A_8113, k2_tarski(A_8114, B_8115), A_8113)=A_8114 | k4_xboole_0(A_8113, k2_tarski(A_8114, B_8115))=A_8113)), inference(resolution, [status(thm)], [c_1440, c_22])).
% 23.49/11.35  tff(c_70594, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_6' | '#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_69806, c_44])).
% 23.49/11.35  tff(c_70816, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_70594])).
% 23.49/11.35  tff(c_70834, plain, (r2_hidden('#skF_5', '#skF_7') | k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_70816, c_163])).
% 23.49/11.35  tff(c_70847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_48, c_70834])).
% 23.49/11.35  tff(c_70848, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_70594])).
% 23.49/11.35  tff(c_70867, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_70848, c_163])).
% 23.49/11.35  tff(c_70880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_46, c_70867])).
% 23.49/11.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.49/11.35  
% 23.49/11.35  Inference rules
% 23.49/11.35  ----------------------
% 23.49/11.35  #Ref     : 0
% 23.49/11.35  #Sup     : 16419
% 23.49/11.35  #Fact    : 22
% 23.49/11.35  #Define  : 0
% 23.49/11.35  #Split   : 4
% 23.49/11.35  #Chain   : 0
% 23.49/11.35  #Close   : 0
% 23.49/11.35  
% 23.49/11.35  Ordering : KBO
% 23.49/11.35  
% 23.49/11.35  Simplification rules
% 23.49/11.35  ----------------------
% 23.49/11.35  #Subsume      : 6997
% 23.49/11.35  #Demod        : 12401
% 23.49/11.35  #Tautology    : 3041
% 23.49/11.35  #SimpNegUnit  : 698
% 23.49/11.35  #BackRed      : 54
% 23.49/11.35  
% 23.49/11.35  #Partial instantiations: 3523
% 23.49/11.35  #Strategies tried      : 1
% 23.49/11.35  
% 23.49/11.35  Timing (in seconds)
% 23.49/11.35  ----------------------
% 23.49/11.35  Preprocessing        : 0.33
% 23.49/11.35  Parsing              : 0.16
% 23.49/11.35  CNF conversion       : 0.03
% 23.49/11.35  Main loop            : 10.23
% 23.49/11.35  Inferencing          : 1.95
% 23.49/11.35  Reduction            : 4.86
% 23.49/11.35  Demodulation         : 4.11
% 23.49/11.35  BG Simplification    : 0.24
% 23.49/11.35  Subsumption          : 2.39
% 23.49/11.35  Abstraction          : 0.49
% 23.49/11.35  MUC search           : 0.00
% 23.49/11.35  Cooper               : 0.00
% 23.49/11.35  Total                : 10.58
% 23.49/11.35  Index Insertion      : 0.00
% 23.49/11.35  Index Deletion       : 0.00
% 23.49/11.35  Index Matching       : 0.00
% 23.49/11.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
