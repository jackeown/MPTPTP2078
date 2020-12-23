%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

tff(c_44,plain,(
    ! [A_67] : k1_ordinal1(A_67) != A_67 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_616,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(B_115,k1_tarski(A_116)) = k1_tarski(A_116)
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_664,plain,(
    ! [B_117,A_118] :
      ( k2_xboole_0(B_117,k1_tarski(A_118)) = B_117
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_4])).

tff(c_42,plain,(
    ! [A_66] : k2_xboole_0(A_66,k1_tarski(A_66)) = k1_ordinal1(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_687,plain,(
    ! [A_118] :
      ( k1_ordinal1(A_118) = A_118
      | ~ r2_hidden(A_118,A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_42])).

tff(c_708,plain,(
    ! [A_118] : ~ r2_hidden(A_118,A_118) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_687])).

tff(c_36,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,k1_tarski(B_61)) = A_60
      | r2_hidden(B_61,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_401,plain,(
    ! [A_100,B_101] : k4_xboole_0(k2_xboole_0(A_100,B_101),B_101) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_436,plain,(
    ! [A_66] : k4_xboole_0(k1_ordinal1(A_66),k1_tarski(A_66)) = k4_xboole_0(A_66,k1_tarski(A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_401])).

tff(c_38,plain,(
    ! [A_62,B_63] : k6_subset_1(A_62,B_63) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_47,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_1027,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_47])).

tff(c_1049,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1027])).

tff(c_1053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_1049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.37  
% 2.84/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.37  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_1
% 2.84/1.37  
% 2.84/1.37  %Foreground sorts:
% 2.84/1.37  
% 2.84/1.37  
% 2.84/1.37  %Background operators:
% 2.84/1.37  
% 2.84/1.37  
% 2.84/1.37  %Foreground operators:
% 2.84/1.37  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.84/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.37  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.84/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.84/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.84/1.37  
% 2.84/1.38  tff(f_73, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.84/1.38  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.84/1.38  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.84/1.38  tff(f_70, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.84/1.38  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.84/1.38  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.84/1.38  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.84/1.38  tff(f_76, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 2.84/1.38  tff(c_44, plain, (![A_67]: (k1_ordinal1(A_67)!=A_67)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.38  tff(c_616, plain, (![B_115, A_116]: (k3_xboole_0(B_115, k1_tarski(A_116))=k1_tarski(A_116) | ~r2_hidden(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.38  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.38  tff(c_664, plain, (![B_117, A_118]: (k2_xboole_0(B_117, k1_tarski(A_118))=B_117 | ~r2_hidden(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_616, c_4])).
% 2.84/1.38  tff(c_42, plain, (![A_66]: (k2_xboole_0(A_66, k1_tarski(A_66))=k1_ordinal1(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.84/1.38  tff(c_687, plain, (![A_118]: (k1_ordinal1(A_118)=A_118 | ~r2_hidden(A_118, A_118))), inference(superposition, [status(thm), theory('equality')], [c_664, c_42])).
% 2.84/1.38  tff(c_708, plain, (![A_118]: (~r2_hidden(A_118, A_118))), inference(negUnitSimplification, [status(thm)], [c_44, c_687])).
% 2.84/1.38  tff(c_36, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k1_tarski(B_61))=A_60 | r2_hidden(B_61, A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.38  tff(c_401, plain, (![A_100, B_101]: (k4_xboole_0(k2_xboole_0(A_100, B_101), B_101)=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.38  tff(c_436, plain, (![A_66]: (k4_xboole_0(k1_ordinal1(A_66), k1_tarski(A_66))=k4_xboole_0(A_66, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_401])).
% 2.84/1.38  tff(c_38, plain, (![A_62, B_63]: (k6_subset_1(A_62, B_63)=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.38  tff(c_46, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.38  tff(c_47, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.84/1.38  tff(c_1027, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_47])).
% 2.84/1.38  tff(c_1049, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1027])).
% 2.84/1.38  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_1049])).
% 2.84/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  
% 2.84/1.38  Inference rules
% 2.84/1.38  ----------------------
% 2.84/1.38  #Ref     : 0
% 2.84/1.38  #Sup     : 247
% 2.84/1.38  #Fact    : 0
% 2.84/1.38  #Define  : 0
% 2.84/1.38  #Split   : 0
% 2.84/1.38  #Chain   : 0
% 2.84/1.38  #Close   : 0
% 2.84/1.38  
% 2.84/1.38  Ordering : KBO
% 2.84/1.38  
% 2.84/1.38  Simplification rules
% 2.84/1.38  ----------------------
% 2.84/1.38  #Subsume      : 14
% 2.84/1.38  #Demod        : 35
% 2.84/1.38  #Tautology    : 157
% 2.84/1.38  #SimpNegUnit  : 3
% 2.84/1.38  #BackRed      : 1
% 2.84/1.38  
% 2.84/1.38  #Partial instantiations: 0
% 2.84/1.38  #Strategies tried      : 1
% 2.84/1.38  
% 2.84/1.38  Timing (in seconds)
% 2.84/1.38  ----------------------
% 2.84/1.39  Preprocessing        : 0.31
% 2.84/1.39  Parsing              : 0.17
% 2.84/1.39  CNF conversion       : 0.02
% 2.84/1.39  Main loop            : 0.32
% 2.84/1.39  Inferencing          : 0.13
% 2.84/1.39  Reduction            : 0.11
% 2.84/1.39  Demodulation         : 0.08
% 2.84/1.39  BG Simplification    : 0.02
% 2.84/1.39  Subsumption          : 0.04
% 2.84/1.39  Abstraction          : 0.02
% 2.84/1.39  MUC search           : 0.00
% 2.84/1.39  Cooper               : 0.00
% 2.84/1.39  Total                : 0.66
% 2.84/1.39  Index Insertion      : 0.00
% 2.84/1.39  Index Deletion       : 0.00
% 2.84/1.39  Index Matching       : 0.00
% 2.84/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
