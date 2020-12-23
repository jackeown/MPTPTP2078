%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  36 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(k1_tarski(A_35),B_36) = k1_tarski(A_35)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [B_50,A_51] :
      ( k5_xboole_0(B_50,k1_tarski(A_51)) = k2_xboole_0(B_50,k1_tarski(A_51))
      | r2_hidden(A_51,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_4])).

tff(c_36,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_36])).

tff(c_153,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_147])).

tff(c_26,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,(
    ! [D_39,B_40,A_41] :
      ( D_39 = B_40
      | D_39 = A_41
      | ~ r2_hidden(D_39,k2_tarski(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [D_39,A_13] :
      ( D_39 = A_13
      | D_39 = A_13
      | ~ r2_hidden(D_39,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_157,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_117])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:07:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.23  
% 1.96/1.23  tff(f_57, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.96/1.23  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.96/1.23  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.96/1.23  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.96/1.23  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.23  tff(f_38, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.96/1.23  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.23  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.96/1.23  tff(c_94, plain, (![A_35, B_36]: (k4_xboole_0(k1_tarski(A_35), B_36)=k1_tarski(A_35) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.23  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.23  tff(c_141, plain, (![B_50, A_51]: (k5_xboole_0(B_50, k1_tarski(A_51))=k2_xboole_0(B_50, k1_tarski(A_51)) | r2_hidden(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_94, c_4])).
% 1.96/1.23  tff(c_36, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.23  tff(c_147, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_36])).
% 1.96/1.23  tff(c_153, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_147])).
% 1.96/1.23  tff(c_26, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.23  tff(c_111, plain, (![D_39, B_40, A_41]: (D_39=B_40 | D_39=A_41 | ~r2_hidden(D_39, k2_tarski(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.96/1.23  tff(c_117, plain, (![D_39, A_13]: (D_39=A_13 | D_39=A_13 | ~r2_hidden(D_39, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_111])).
% 1.96/1.23  tff(c_157, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_153, c_117])).
% 1.96/1.23  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_157])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 26
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 0
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 0
% 1.96/1.23  #Demod        : 2
% 1.96/1.23  #Tautology    : 21
% 1.96/1.23  #SimpNegUnit  : 1
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.96/1.24  Preprocessing        : 0.29
% 1.96/1.24  Parsing              : 0.14
% 1.96/1.24  CNF conversion       : 0.02
% 1.96/1.24  Main loop            : 0.12
% 1.96/1.24  Inferencing          : 0.05
% 1.96/1.24  Reduction            : 0.04
% 1.96/1.24  Demodulation         : 0.03
% 1.96/1.24  BG Simplification    : 0.01
% 1.96/1.24  Subsumption          : 0.02
% 1.96/1.24  Abstraction          : 0.01
% 1.96/1.24  MUC search           : 0.00
% 1.96/1.24  Cooper               : 0.00
% 1.96/1.24  Total                : 0.43
% 1.96/1.24  Index Insertion      : 0.00
% 1.96/1.24  Index Deletion       : 0.00
% 1.96/1.24  Index Matching       : 0.00
% 1.96/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
