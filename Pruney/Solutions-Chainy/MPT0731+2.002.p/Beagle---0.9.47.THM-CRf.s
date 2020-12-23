%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_42,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_24,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [D_16,B_17] : r2_hidden(D_16,k2_tarski(D_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_44])).

tff(c_127,plain,(
    ! [B_30,A_31] :
      ( ~ r1_tarski(B_30,A_31)
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_11] : ~ r1_tarski(k1_tarski(A_11),A_11) ),
    inference(resolution,[status(thm)],[c_47,c_127])).

tff(c_30,plain,(
    k1_ordinal1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_tarski(A_12)) = k1_ordinal1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(B_28,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_123,plain,(
    ! [A_29] : r1_tarski(k1_tarski(A_29),k1_ordinal1(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_110])).

tff(c_126,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_123])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:37:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.14  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.14  
% 1.70/1.15  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.70/1.15  tff(f_38, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.70/1.15  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.70/1.15  tff(f_51, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.70/1.15  tff(f_42, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.70/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.70/1.15  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.70/1.15  tff(c_24, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.15  tff(c_44, plain, (![D_16, B_17]: (r2_hidden(D_16, k2_tarski(D_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.15  tff(c_47, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_44])).
% 1.70/1.15  tff(c_127, plain, (![B_30, A_31]: (~r1_tarski(B_30, A_31) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.15  tff(c_138, plain, (![A_11]: (~r1_tarski(k1_tarski(A_11), A_11))), inference(resolution, [status(thm)], [c_47, c_127])).
% 1.70/1.15  tff(c_30, plain, (k1_ordinal1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.15  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, k1_tarski(A_12))=k1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.15  tff(c_71, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.15  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.15  tff(c_110, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(B_28, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 1.70/1.15  tff(c_123, plain, (![A_29]: (r1_tarski(k1_tarski(A_29), k1_ordinal1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_110])).
% 1.70/1.15  tff(c_126, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_123])).
% 1.70/1.15  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_126])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 30
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 4
% 1.70/1.15  #Tautology    : 20
% 1.70/1.15  #SimpNegUnit  : 1
% 1.70/1.15  #BackRed      : 1
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.15  Preprocessing        : 0.29
% 1.70/1.15  Parsing              : 0.15
% 1.70/1.15  CNF conversion       : 0.02
% 1.70/1.15  Main loop            : 0.12
% 1.70/1.15  Inferencing          : 0.04
% 1.70/1.15  Reduction            : 0.04
% 1.70/1.15  Demodulation         : 0.03
% 1.70/1.15  BG Simplification    : 0.01
% 1.70/1.15  Subsumption          : 0.02
% 1.70/1.15  Abstraction          : 0.01
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.43
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.15  Index Matching       : 0.00
% 1.70/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
