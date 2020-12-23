%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.29s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(c_44,plain,(
    ! [A_67] : k1_ordinal1(A_67) != A_67 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_616,plain,(
    ! [B_115,A_116] :
      ( k3_xboole_0(B_115,k1_tarski(A_116)) = k1_tarski(A_116)
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.47  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_1
% 3.29/1.47  
% 3.29/1.47  %Foreground sorts:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Background operators:
% 3.29/1.47  
% 3.29/1.47  
% 3.29/1.47  %Foreground operators:
% 3.29/1.47  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.29/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.29/1.47  
% 3.29/1.48  tff(f_73, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 3.29/1.48  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 3.29/1.48  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.29/1.48  tff(f_70, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.29/1.48  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.29/1.48  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.29/1.48  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.29/1.48  tff(f_76, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 3.29/1.48  tff(c_44, plain, (![A_67]: (k1_ordinal1(A_67)!=A_67)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.48  tff(c_616, plain, (![B_115, A_116]: (k3_xboole_0(B_115, k1_tarski(A_116))=k1_tarski(A_116) | ~r2_hidden(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.48  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.48  tff(c_664, plain, (![B_117, A_118]: (k2_xboole_0(B_117, k1_tarski(A_118))=B_117 | ~r2_hidden(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_616, c_4])).
% 3.29/1.48  tff(c_42, plain, (![A_66]: (k2_xboole_0(A_66, k1_tarski(A_66))=k1_ordinal1(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.48  tff(c_687, plain, (![A_118]: (k1_ordinal1(A_118)=A_118 | ~r2_hidden(A_118, A_118))), inference(superposition, [status(thm), theory('equality')], [c_664, c_42])).
% 3.29/1.48  tff(c_708, plain, (![A_118]: (~r2_hidden(A_118, A_118))), inference(negUnitSimplification, [status(thm)], [c_44, c_687])).
% 3.29/1.48  tff(c_36, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k1_tarski(B_61))=A_60 | r2_hidden(B_61, A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.48  tff(c_401, plain, (![A_100, B_101]: (k4_xboole_0(k2_xboole_0(A_100, B_101), B_101)=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.48  tff(c_436, plain, (![A_66]: (k4_xboole_0(k1_ordinal1(A_66), k1_tarski(A_66))=k4_xboole_0(A_66, k1_tarski(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_401])).
% 3.29/1.48  tff(c_38, plain, (![A_62, B_63]: (k6_subset_1(A_62, B_63)=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.48  tff(c_46, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.48  tff(c_47, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 3.29/1.48  tff(c_1027, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_47])).
% 3.29/1.48  tff(c_1049, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1027])).
% 3.29/1.48  tff(c_1053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_1049])).
% 3.29/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  Inference rules
% 3.29/1.48  ----------------------
% 3.29/1.48  #Ref     : 0
% 3.29/1.48  #Sup     : 247
% 3.29/1.48  #Fact    : 0
% 3.29/1.48  #Define  : 0
% 3.29/1.48  #Split   : 0
% 3.29/1.48  #Chain   : 0
% 3.29/1.48  #Close   : 0
% 3.29/1.48  
% 3.29/1.48  Ordering : KBO
% 3.29/1.48  
% 3.29/1.48  Simplification rules
% 3.29/1.48  ----------------------
% 3.29/1.48  #Subsume      : 14
% 3.29/1.48  #Demod        : 35
% 3.29/1.48  #Tautology    : 157
% 3.29/1.48  #SimpNegUnit  : 3
% 3.29/1.48  #BackRed      : 1
% 3.29/1.48  
% 3.29/1.48  #Partial instantiations: 0
% 3.29/1.48  #Strategies tried      : 1
% 3.29/1.48  
% 3.29/1.48  Timing (in seconds)
% 3.29/1.48  ----------------------
% 3.29/1.49  Preprocessing        : 0.36
% 3.29/1.49  Parsing              : 0.19
% 3.29/1.49  CNF conversion       : 0.02
% 3.29/1.49  Main loop            : 0.33
% 3.29/1.49  Inferencing          : 0.13
% 3.29/1.49  Reduction            : 0.11
% 3.29/1.49  Demodulation         : 0.09
% 3.29/1.49  BG Simplification    : 0.03
% 3.29/1.49  Subsumption          : 0.04
% 3.29/1.49  Abstraction          : 0.02
% 3.29/1.49  MUC search           : 0.00
% 3.29/1.49  Cooper               : 0.00
% 3.29/1.49  Total                : 0.72
% 3.29/1.49  Index Insertion      : 0.00
% 3.29/1.49  Index Deletion       : 0.00
% 3.29/1.49  Index Matching       : 0.00
% 3.29/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
