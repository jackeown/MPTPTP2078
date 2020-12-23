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
% DateTime   : Thu Dec  3 09:49:02 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | k3_xboole_0(A_40,k1_tarski(B_39)) != k1_tarski(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | k3_xboole_0(k1_tarski(B_44),A_45) != k1_tarski(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_158,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_146])).

tff(c_6,plain,(
    ! [D_10,B_6,A_5] :
      ( D_10 = B_6
      | D_10 = A_5
      | ~ r2_hidden(D_10,k2_tarski(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_161,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_158,c_6])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.91/1.26  
% 1.91/1.26  %Foreground sorts:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Background operators:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Foreground operators:
% 1.91/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.26  
% 1.91/1.27  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.91/1.27  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.91/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.91/1.27  tff(f_50, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 1.91/1.27  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.27  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.27  tff(c_32, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.27  tff(c_36, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.27  tff(c_89, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.27  tff(c_93, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_36, c_89])).
% 1.91/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.27  tff(c_136, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | k3_xboole_0(A_40, k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.27  tff(c_146, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | k3_xboole_0(k1_tarski(B_44), A_45)!=k1_tarski(B_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 1.91/1.27  tff(c_158, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_146])).
% 1.91/1.27  tff(c_6, plain, (![D_10, B_6, A_5]: (D_10=B_6 | D_10=A_5 | ~r2_hidden(D_10, k2_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.27  tff(c_161, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_158, c_6])).
% 1.91/1.27  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_161])).
% 1.91/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.27  
% 1.91/1.27  Inference rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Ref     : 0
% 1.91/1.27  #Sup     : 29
% 1.91/1.27  #Fact    : 0
% 1.91/1.27  #Define  : 0
% 1.91/1.27  #Split   : 0
% 1.91/1.27  #Chain   : 0
% 1.91/1.27  #Close   : 0
% 1.91/1.27  
% 1.91/1.27  Ordering : KBO
% 1.91/1.27  
% 1.91/1.27  Simplification rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Subsume      : 2
% 1.91/1.27  #Demod        : 1
% 1.91/1.27  #Tautology    : 20
% 1.91/1.27  #SimpNegUnit  : 1
% 1.91/1.27  #BackRed      : 0
% 1.91/1.27  
% 1.91/1.27  #Partial instantiations: 0
% 1.91/1.27  #Strategies tried      : 1
% 1.91/1.27  
% 1.91/1.27  Timing (in seconds)
% 1.91/1.27  ----------------------
% 1.91/1.27  Preprocessing        : 0.32
% 1.91/1.27  Parsing              : 0.16
% 1.91/1.27  CNF conversion       : 0.02
% 1.91/1.27  Main loop            : 0.14
% 1.91/1.27  Inferencing          : 0.05
% 1.91/1.27  Reduction            : 0.05
% 1.91/1.27  Demodulation         : 0.04
% 1.91/1.27  BG Simplification    : 0.01
% 1.91/1.27  Subsumption          : 0.03
% 1.91/1.27  Abstraction          : 0.01
% 1.91/1.27  MUC search           : 0.00
% 1.91/1.28  Cooper               : 0.00
% 1.91/1.28  Total                : 0.48
% 1.91/1.28  Index Insertion      : 0.00
% 1.91/1.28  Index Deletion       : 0.00
% 1.91/1.28  Index Matching       : 0.00
% 1.91/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
