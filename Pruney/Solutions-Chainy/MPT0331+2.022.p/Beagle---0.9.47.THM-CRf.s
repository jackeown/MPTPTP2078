%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 45.35s
% Output     : CNFRefutation 45.35s
% Verified   : 
% Statistics : Number of formulae       :   42 (  81 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 178 expanded)
%              Number of equality atoms :   31 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_179,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r2_hidden('#skF_1'(A_60,B_61,C_62),C_62)
      | r2_hidden('#skF_2'(A_60,B_61,C_62),C_62)
      | k4_xboole_0(A_60,B_61) = C_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_179])).

tff(c_1069,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_1'(A_123,B_124,C_125),A_123)
      | r2_hidden('#skF_2'(A_123,B_124,C_125),B_124)
      | ~ r2_hidden('#skF_2'(A_123,B_124,C_125),A_123)
      | k4_xboole_0(A_123,B_124) = C_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2144,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_2'(A_160,B_161,A_160),B_161)
      | ~ r2_hidden('#skF_2'(A_160,B_161,A_160),A_160)
      | k4_xboole_0(A_160,B_161) = A_160 ) ),
    inference(resolution,[status(thm)],[c_1069,c_8])).

tff(c_2162,plain,(
    ! [A_162,B_163] :
      ( r2_hidden('#skF_2'(A_162,B_163,A_162),B_163)
      | k4_xboole_0(A_162,B_163) = A_162 ) ),
    inference(resolution,[status(thm)],[c_188,c_2144])).

tff(c_46,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,(
    ! [E_50,C_51,B_52,A_53] :
      ( E_50 = C_51
      | E_50 = B_52
      | E_50 = A_53
      | ~ r2_hidden(E_50,k1_enumset1(A_53,B_52,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [E_50,B_17,A_16] :
      ( E_50 = B_17
      | E_50 = A_16
      | E_50 = A_16
      | ~ r2_hidden(E_50,k2_tarski(A_16,B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_159865,plain,(
    ! [A_12471,A_12472,B_12473] :
      ( '#skF_2'(A_12471,k2_tarski(A_12472,B_12473),A_12471) = B_12473
      | '#skF_2'(A_12471,k2_tarski(A_12472,B_12473),A_12471) = A_12472
      | k4_xboole_0(A_12471,k2_tarski(A_12472,B_12473)) = A_12471 ) ),
    inference(resolution,[status(thm)],[c_2162,c_111])).

tff(c_161566,plain,
    ( '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_6'
    | '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_159865,c_50])).

tff(c_161581,plain,(
    '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_161566])).

tff(c_161599,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_161581,c_188])).

tff(c_161615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_54,c_161599])).

tff(c_161616,plain,(
    '#skF_2'('#skF_7',k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_161566])).

tff(c_161635,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_161616,c_188])).

tff(c_161651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_52,c_161635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 45.35/31.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.35/31.14  
% 45.35/31.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.35/31.14  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 45.35/31.14  
% 45.35/31.14  %Foreground sorts:
% 45.35/31.14  
% 45.35/31.14  
% 45.35/31.14  %Background operators:
% 45.35/31.14  
% 45.35/31.14  
% 45.35/31.14  %Foreground operators:
% 45.35/31.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 45.35/31.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 45.35/31.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 45.35/31.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 45.35/31.14  tff('#skF_7', type, '#skF_7': $i).
% 45.35/31.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 45.35/31.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 45.35/31.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 45.35/31.14  tff('#skF_5', type, '#skF_5': $i).
% 45.35/31.14  tff('#skF_6', type, '#skF_6': $i).
% 45.35/31.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 45.35/31.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 45.35/31.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 45.35/31.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 45.35/31.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 45.35/31.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 45.35/31.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 45.35/31.14  
% 45.35/31.16  tff(f_67, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 45.35/31.16  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 45.35/31.16  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 45.35/31.16  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 45.35/31.16  tff(c_50, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_67])).
% 45.35/31.16  tff(c_52, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 45.35/31.16  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 45.35/31.16  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.35/31.16  tff(c_179, plain, (![A_60, B_61, C_62]: (~r2_hidden('#skF_1'(A_60, B_61, C_62), C_62) | r2_hidden('#skF_2'(A_60, B_61, C_62), C_62) | k4_xboole_0(A_60, B_61)=C_62)), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.35/31.16  tff(c_188, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_179])).
% 45.35/31.16  tff(c_1069, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_1'(A_123, B_124, C_125), A_123) | r2_hidden('#skF_2'(A_123, B_124, C_125), B_124) | ~r2_hidden('#skF_2'(A_123, B_124, C_125), A_123) | k4_xboole_0(A_123, B_124)=C_125)), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.35/31.16  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 45.35/31.16  tff(c_2144, plain, (![A_160, B_161]: (r2_hidden('#skF_2'(A_160, B_161, A_160), B_161) | ~r2_hidden('#skF_2'(A_160, B_161, A_160), A_160) | k4_xboole_0(A_160, B_161)=A_160)), inference(resolution, [status(thm)], [c_1069, c_8])).
% 45.35/31.16  tff(c_2162, plain, (![A_162, B_163]: (r2_hidden('#skF_2'(A_162, B_163, A_162), B_163) | k4_xboole_0(A_162, B_163)=A_162)), inference(resolution, [status(thm)], [c_188, c_2144])).
% 45.35/31.16  tff(c_46, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 45.35/31.16  tff(c_108, plain, (![E_50, C_51, B_52, A_53]: (E_50=C_51 | E_50=B_52 | E_50=A_53 | ~r2_hidden(E_50, k1_enumset1(A_53, B_52, C_51)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 45.35/31.16  tff(c_111, plain, (![E_50, B_17, A_16]: (E_50=B_17 | E_50=A_16 | E_50=A_16 | ~r2_hidden(E_50, k2_tarski(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_108])).
% 45.35/31.16  tff(c_159865, plain, (![A_12471, A_12472, B_12473]: ('#skF_2'(A_12471, k2_tarski(A_12472, B_12473), A_12471)=B_12473 | '#skF_2'(A_12471, k2_tarski(A_12472, B_12473), A_12471)=A_12472 | k4_xboole_0(A_12471, k2_tarski(A_12472, B_12473))=A_12471)), inference(resolution, [status(thm)], [c_2162, c_111])).
% 45.35/31.16  tff(c_161566, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_6' | '#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_159865, c_50])).
% 45.35/31.16  tff(c_161581, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_161566])).
% 45.35/31.16  tff(c_161599, plain, (r2_hidden('#skF_5', '#skF_7') | k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_161581, c_188])).
% 45.35/31.16  tff(c_161615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_54, c_161599])).
% 45.35/31.16  tff(c_161616, plain, ('#skF_2'('#skF_7', k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_161566])).
% 45.35/31.16  tff(c_161635, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_161616, c_188])).
% 45.35/31.16  tff(c_161651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_52, c_161635])).
% 45.35/31.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 45.35/31.16  
% 45.35/31.16  Inference rules
% 45.35/31.16  ----------------------
% 45.35/31.16  #Ref     : 0
% 45.35/31.16  #Sup     : 39546
% 45.35/31.16  #Fact    : 78
% 45.35/31.16  #Define  : 0
% 45.35/31.16  #Split   : 4
% 45.35/31.16  #Chain   : 0
% 45.35/31.16  #Close   : 0
% 45.35/31.16  
% 45.35/31.16  Ordering : KBO
% 45.35/31.16  
% 45.35/31.16  Simplification rules
% 45.35/31.16  ----------------------
% 45.35/31.16  #Subsume      : 18238
% 45.35/31.16  #Demod        : 21423
% 45.35/31.16  #Tautology    : 6057
% 45.35/31.16  #SimpNegUnit  : 2268
% 45.35/31.16  #BackRed      : 3
% 45.35/31.16  
% 45.35/31.16  #Partial instantiations: 5109
% 45.35/31.16  #Strategies tried      : 1
% 45.35/31.16  
% 45.35/31.16  Timing (in seconds)
% 45.35/31.16  ----------------------
% 45.35/31.17  Preprocessing        : 0.29
% 45.35/31.17  Parsing              : 0.14
% 45.35/31.17  CNF conversion       : 0.02
% 45.35/31.17  Main loop            : 30.04
% 45.35/31.17  Inferencing          : 4.26
% 45.35/31.17  Reduction            : 17.21
% 45.35/31.17  Demodulation         : 15.31
% 45.35/31.17  BG Simplification    : 0.54
% 45.35/31.17  Subsumption          : 6.66
% 45.35/31.17  Abstraction          : 1.18
% 45.35/31.17  MUC search           : 0.00
% 45.35/31.17  Cooper               : 0.00
% 45.35/31.17  Total                : 30.37
% 45.35/31.17  Index Insertion      : 0.00
% 45.35/31.17  Index Deletion       : 0.00
% 45.35/31.17  Index Matching       : 0.00
% 45.35/31.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
