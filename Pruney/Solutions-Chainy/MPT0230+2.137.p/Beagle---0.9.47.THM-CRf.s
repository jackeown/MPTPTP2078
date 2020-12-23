%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:13 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  46 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [B_26] : k4_xboole_0(k1_tarski(B_26),k1_tarski(B_26)) != k1_tarski(B_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_46,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_4])).

tff(c_117,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_114])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k1_tarski(A_23),B_24) = k1_tarski(A_23)
      | r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_168,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k1_tarski('#skF_3')
    | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_36])).

tff(c_174,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_168])).

tff(c_8,plain,(
    ! [D_12,B_8,A_7] :
      ( D_12 = B_8
      | D_12 = A_7
      | ~ r2_hidden(D_12,k2_tarski(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_179,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_174,c_8])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.29  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.01/1.29  
% 2.01/1.29  %Foreground sorts:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Background operators:
% 2.01/1.29  
% 2.01/1.29  
% 2.01/1.29  %Foreground operators:
% 2.01/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.29  
% 2.01/1.30  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.01/1.30  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.01/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.01/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.01/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.01/1.30  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.01/1.30  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.30  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.30  tff(c_42, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.30  tff(c_38, plain, (![B_26]: (k4_xboole_0(k1_tarski(B_26), k1_tarski(B_26))!=k1_tarski(B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.30  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.30  tff(c_90, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.30  tff(c_99, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 2.01/1.30  tff(c_46, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.30  tff(c_75, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.30  tff(c_79, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_46, c_75])).
% 2.01/1.30  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.30  tff(c_114, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_4])).
% 2.01/1.30  tff(c_117, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_114])).
% 2.01/1.30  tff(c_36, plain, (![A_23, B_24]: (k4_xboole_0(k1_tarski(A_23), B_24)=k1_tarski(A_23) | r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.30  tff(c_168, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k1_tarski('#skF_3') | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_36])).
% 2.01/1.30  tff(c_174, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_38, c_168])).
% 2.01/1.30  tff(c_8, plain, (![D_12, B_8, A_7]: (D_12=B_8 | D_12=A_7 | ~r2_hidden(D_12, k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.30  tff(c_179, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_174, c_8])).
% 2.01/1.30  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_179])).
% 2.01/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.30  
% 2.01/1.30  Inference rules
% 2.01/1.30  ----------------------
% 2.01/1.30  #Ref     : 0
% 2.01/1.30  #Sup     : 32
% 2.01/1.30  #Fact    : 0
% 2.01/1.30  #Define  : 0
% 2.01/1.30  #Split   : 0
% 2.01/1.30  #Chain   : 0
% 2.01/1.30  #Close   : 0
% 2.01/1.30  
% 2.01/1.30  Ordering : KBO
% 2.01/1.30  
% 2.01/1.30  Simplification rules
% 2.01/1.30  ----------------------
% 2.01/1.30  #Subsume      : 1
% 2.01/1.30  #Demod        : 3
% 2.01/1.30  #Tautology    : 23
% 2.01/1.30  #SimpNegUnit  : 3
% 2.01/1.30  #BackRed      : 0
% 2.01/1.30  
% 2.01/1.30  #Partial instantiations: 0
% 2.01/1.30  #Strategies tried      : 1
% 2.01/1.30  
% 2.01/1.30  Timing (in seconds)
% 2.01/1.30  ----------------------
% 2.01/1.31  Preprocessing        : 0.35
% 2.01/1.31  Parsing              : 0.18
% 2.01/1.31  CNF conversion       : 0.03
% 2.01/1.31  Main loop            : 0.14
% 2.01/1.31  Inferencing          : 0.05
% 2.01/1.31  Reduction            : 0.05
% 2.01/1.31  Demodulation         : 0.04
% 2.01/1.31  BG Simplification    : 0.02
% 2.01/1.31  Subsumption          : 0.03
% 2.01/1.31  Abstraction          : 0.01
% 2.01/1.31  MUC search           : 0.00
% 2.01/1.31  Cooper               : 0.00
% 2.01/1.31  Total                : 0.52
% 2.01/1.31  Index Insertion      : 0.00
% 2.01/1.31  Index Deletion       : 0.00
% 2.01/1.31  Index Matching       : 0.00
% 2.01/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
