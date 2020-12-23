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
% DateTime   : Thu Dec  3 09:48:03 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),k1_tarski(B_22)) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_36])).

tff(c_16,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_16])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_78])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.72/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.16  
% 1.72/1.16  tff(f_48, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.72/1.16  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.72/1.16  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.72/1.16  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.72/1.16  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.16  tff(c_50, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(B_22))=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.16  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.72/1.16  tff(c_56, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_36])).
% 1.72/1.16  tff(c_16, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.16  tff(c_68, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_16])).
% 1.72/1.16  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.16  tff(c_78, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.72/1.16  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_78])).
% 1.72/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  Inference rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Ref     : 0
% 1.72/1.16  #Sup     : 12
% 1.72/1.16  #Fact    : 0
% 1.72/1.16  #Define  : 0
% 1.72/1.16  #Split   : 0
% 1.72/1.16  #Chain   : 0
% 1.72/1.16  #Close   : 0
% 1.72/1.16  
% 1.72/1.16  Ordering : KBO
% 1.72/1.16  
% 1.72/1.16  Simplification rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Subsume      : 0
% 1.72/1.16  #Demod        : 1
% 1.72/1.16  #Tautology    : 8
% 1.72/1.16  #SimpNegUnit  : 1
% 1.72/1.16  #BackRed      : 0
% 1.72/1.16  
% 1.72/1.16  #Partial instantiations: 0
% 1.72/1.16  #Strategies tried      : 1
% 1.72/1.16  
% 1.72/1.16  Timing (in seconds)
% 1.72/1.16  ----------------------
% 1.72/1.17  Preprocessing        : 0.28
% 1.72/1.17  Parsing              : 0.15
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.08
% 1.72/1.17  Inferencing          : 0.02
% 1.72/1.17  Reduction            : 0.03
% 1.72/1.17  Demodulation         : 0.02
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.02
% 1.72/1.17  Abstraction          : 0.00
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.39
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
