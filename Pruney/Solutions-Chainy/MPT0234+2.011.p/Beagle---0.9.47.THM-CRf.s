%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:42 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),B_35) = k1_tarski(A_34)
      | r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [B_41,A_42] :
      ( k5_xboole_0(B_41,k1_tarski(A_42)) = k2_xboole_0(B_41,k1_tarski(A_42))
      | r2_hidden(A_42,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_4])).

tff(c_30,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4')
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_30])).

tff(c_124,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_118])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_128,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.21  
% 1.73/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.21  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.73/1.21  
% 1.73/1.21  %Foreground sorts:
% 1.73/1.21  
% 1.73/1.21  
% 1.73/1.21  %Background operators:
% 1.73/1.21  
% 1.73/1.21  
% 1.73/1.21  %Foreground operators:
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.73/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.73/1.21  
% 1.73/1.22  tff(f_55, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.73/1.22  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.73/1.22  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.73/1.22  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.73/1.22  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.73/1.22  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.22  tff(c_18, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.22  tff(c_86, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), B_35)=k1_tarski(A_34) | r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.22  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.22  tff(c_112, plain, (![B_41, A_42]: (k5_xboole_0(B_41, k1_tarski(A_42))=k2_xboole_0(B_41, k1_tarski(A_42)) | r2_hidden(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_86, c_4])).
% 1.73/1.22  tff(c_30, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.22  tff(c_118, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4') | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_30])).
% 1.73/1.22  tff(c_124, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_118])).
% 1.73/1.22  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.73/1.22  tff(c_128, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_124, c_6])).
% 1.73/1.22  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_128])).
% 1.73/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.22  
% 1.73/1.22  Inference rules
% 1.73/1.22  ----------------------
% 1.73/1.22  #Ref     : 0
% 1.73/1.22  #Sup     : 21
% 1.73/1.22  #Fact    : 0
% 1.73/1.22  #Define  : 0
% 1.73/1.22  #Split   : 0
% 1.73/1.22  #Chain   : 0
% 1.73/1.22  #Close   : 0
% 1.73/1.22  
% 1.73/1.22  Ordering : KBO
% 1.73/1.22  
% 1.73/1.22  Simplification rules
% 1.73/1.22  ----------------------
% 1.73/1.22  #Subsume      : 0
% 1.73/1.22  #Demod        : 1
% 1.73/1.22  #Tautology    : 18
% 1.73/1.22  #SimpNegUnit  : 1
% 1.73/1.22  #BackRed      : 0
% 1.73/1.22  
% 1.73/1.22  #Partial instantiations: 0
% 1.73/1.22  #Strategies tried      : 1
% 1.73/1.22  
% 1.73/1.22  Timing (in seconds)
% 1.73/1.22  ----------------------
% 1.73/1.22  Preprocessing        : 0.30
% 1.73/1.22  Parsing              : 0.16
% 1.73/1.22  CNF conversion       : 0.02
% 1.73/1.22  Main loop            : 0.11
% 1.73/1.22  Inferencing          : 0.04
% 1.73/1.22  Reduction            : 0.03
% 1.73/1.22  Demodulation         : 0.02
% 1.73/1.22  BG Simplification    : 0.01
% 1.73/1.22  Subsumption          : 0.02
% 1.73/1.22  Abstraction          : 0.01
% 1.73/1.22  MUC search           : 0.00
% 1.73/1.22  Cooper               : 0.00
% 1.73/1.22  Total                : 0.43
% 1.73/1.22  Index Insertion      : 0.00
% 1.73/1.22  Index Deletion       : 0.00
% 1.73/1.22  Index Matching       : 0.00
% 1.73/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
