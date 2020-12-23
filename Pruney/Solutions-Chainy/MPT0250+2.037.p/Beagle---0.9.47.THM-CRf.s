%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  62 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_50,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [D_34,B_35] : r2_hidden(D_34,k2_tarski(D_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_182,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_188,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_182])).

tff(c_197,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_188])).

tff(c_279,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k4_xboole_0(A_69,B_70),C_71) = k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_361,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( ~ r2_hidden(D_85,C_86)
      | ~ r2_hidden(D_85,k4_xboole_0(A_87,k2_xboole_0(B_88,C_86))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_6])).

tff(c_383,plain,(
    ! [D_89,A_90] :
      ( ~ r2_hidden(D_89,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_89,k4_xboole_0(A_90,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_361])).

tff(c_434,plain,(
    ! [D_101,A_102] :
      ( ~ r2_hidden(D_101,k1_tarski('#skF_5'))
      | r2_hidden(D_101,'#skF_6')
      | ~ r2_hidden(D_101,A_102) ) ),
    inference(resolution,[status(thm)],[c_4,c_383])).

tff(c_437,plain,(
    ! [A_102] :
      ( r2_hidden('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_5',A_102) ) ),
    inference(resolution,[status(thm)],[c_77,c_434])).

tff(c_441,plain,(
    ! [A_103] : ~ r2_hidden('#skF_5',A_103) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_437])).

tff(c_458,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_77,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.44  
% 2.46/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.78/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.44  
% 2.78/1.45  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.45  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.78/1.45  tff(f_69, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.78/1.45  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.78/1.45  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.78/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.78/1.45  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.45  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.78/1.45  tff(c_50, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.45  tff(c_74, plain, (![D_34, B_35]: (r2_hidden(D_34, k2_tarski(D_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.45  tff(c_77, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_74])).
% 2.78/1.45  tff(c_58, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.45  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.45  tff(c_30, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.45  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.45  tff(c_62, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 2.78/1.45  tff(c_182, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.45  tff(c_188, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_182])).
% 2.78/1.45  tff(c_197, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_188])).
% 2.78/1.45  tff(c_279, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k4_xboole_0(A_69, B_70), C_71)=k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.45  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.45  tff(c_361, plain, (![D_85, C_86, A_87, B_88]: (~r2_hidden(D_85, C_86) | ~r2_hidden(D_85, k4_xboole_0(A_87, k2_xboole_0(B_88, C_86))))), inference(superposition, [status(thm), theory('equality')], [c_279, c_6])).
% 2.78/1.45  tff(c_383, plain, (![D_89, A_90]: (~r2_hidden(D_89, k1_tarski('#skF_5')) | ~r2_hidden(D_89, k4_xboole_0(A_90, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_361])).
% 2.78/1.45  tff(c_434, plain, (![D_101, A_102]: (~r2_hidden(D_101, k1_tarski('#skF_5')) | r2_hidden(D_101, '#skF_6') | ~r2_hidden(D_101, A_102))), inference(resolution, [status(thm)], [c_4, c_383])).
% 2.78/1.45  tff(c_437, plain, (![A_102]: (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', A_102))), inference(resolution, [status(thm)], [c_77, c_434])).
% 2.78/1.45  tff(c_441, plain, (![A_103]: (~r2_hidden('#skF_5', A_103))), inference(negUnitSimplification, [status(thm)], [c_58, c_437])).
% 2.78/1.45  tff(c_458, plain, $false, inference(resolution, [status(thm)], [c_77, c_441])).
% 2.78/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  Inference rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Ref     : 0
% 2.78/1.45  #Sup     : 96
% 2.78/1.45  #Fact    : 0
% 2.78/1.45  #Define  : 0
% 2.78/1.45  #Split   : 1
% 2.78/1.45  #Chain   : 0
% 2.78/1.45  #Close   : 0
% 2.78/1.45  
% 2.78/1.45  Ordering : KBO
% 2.78/1.45  
% 2.78/1.45  Simplification rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Subsume      : 23
% 2.78/1.45  #Demod        : 25
% 2.78/1.45  #Tautology    : 39
% 2.78/1.45  #SimpNegUnit  : 2
% 2.78/1.45  #BackRed      : 1
% 2.78/1.45  
% 2.78/1.45  #Partial instantiations: 0
% 2.78/1.45  #Strategies tried      : 1
% 2.78/1.45  
% 2.78/1.45  Timing (in seconds)
% 2.78/1.45  ----------------------
% 2.78/1.46  Preprocessing        : 0.33
% 2.78/1.46  Parsing              : 0.17
% 2.78/1.46  CNF conversion       : 0.02
% 2.78/1.46  Main loop            : 0.31
% 2.78/1.46  Inferencing          : 0.11
% 2.78/1.46  Reduction            : 0.11
% 2.78/1.46  Demodulation         : 0.09
% 2.78/1.46  BG Simplification    : 0.02
% 2.78/1.46  Subsumption          : 0.06
% 2.78/1.46  Abstraction          : 0.02
% 2.78/1.46  MUC search           : 0.00
% 2.78/1.46  Cooper               : 0.00
% 2.78/1.46  Total                : 0.68
% 2.78/1.46  Index Insertion      : 0.00
% 2.78/1.46  Index Deletion       : 0.00
% 2.78/1.46  Index Matching       : 0.00
% 2.78/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
