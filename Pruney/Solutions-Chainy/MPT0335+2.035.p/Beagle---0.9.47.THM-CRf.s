%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:58 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  61 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_24,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k1_tarski(A_17),B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_xboole_0
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),k1_xboole_0) = k3_xboole_0(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_12])).

tff(c_1095,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(k1_tarski(A_66),B_67) = k1_tarski(A_66)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_213])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1506,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(B_71,k1_tarski(A_72)) = k1_tarski(A_72)
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_2])).

tff(c_28,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_117])).

tff(c_143,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_143])).

tff(c_164,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_158])).

tff(c_243,plain,(
    ! [A_42,B_43,C_44] : k3_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k3_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_389,plain,(
    ! [C_50] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_50)) = k3_xboole_0('#skF_1',C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_243])).

tff(c_409,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_389])).

tff(c_1558,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_409])).

tff(c_1620,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1558])).

tff(c_1622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.58  
% 3.41/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.58  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.41/1.58  
% 3.41/1.58  %Foreground sorts:
% 3.41/1.58  
% 3.41/1.58  
% 3.41/1.58  %Background operators:
% 3.41/1.58  
% 3.41/1.58  
% 3.41/1.58  %Foreground operators:
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.58  
% 3.41/1.59  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 3.41/1.59  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.41/1.59  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.41/1.59  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.41/1.59  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.41/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.41/1.59  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.41/1.59  tff(c_24, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.41/1.59  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.41/1.59  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.59  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), B_18) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.41/1.59  tff(c_117, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.59  tff(c_203, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_xboole_0 | ~r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_22, c_117])).
% 3.41/1.59  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.41/1.59  tff(c_213, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), k1_xboole_0)=k3_xboole_0(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_203, c_12])).
% 3.41/1.59  tff(c_1095, plain, (![A_66, B_67]: (k3_xboole_0(k1_tarski(A_66), B_67)=k1_tarski(A_66) | ~r2_hidden(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_213])).
% 3.41/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.59  tff(c_1506, plain, (![B_71, A_72]: (k3_xboole_0(B_71, k1_tarski(A_72))=k1_tarski(A_72) | ~r2_hidden(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_1095, c_2])).
% 3.41/1.59  tff(c_28, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.41/1.59  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.41/1.59  tff(c_129, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_117])).
% 3.41/1.59  tff(c_143, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.41/1.59  tff(c_158, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_143])).
% 3.41/1.59  tff(c_164, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_158])).
% 3.41/1.59  tff(c_243, plain, (![A_42, B_43, C_44]: (k3_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k3_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.41/1.59  tff(c_389, plain, (![C_50]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_50))=k3_xboole_0('#skF_1', C_50))), inference(superposition, [status(thm), theory('equality')], [c_164, c_243])).
% 3.41/1.59  tff(c_409, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_389])).
% 3.41/1.59  tff(c_1558, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1506, c_409])).
% 3.41/1.59  tff(c_1620, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1558])).
% 3.41/1.59  tff(c_1622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1620])).
% 3.41/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.59  
% 3.41/1.59  Inference rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Ref     : 0
% 3.41/1.59  #Sup     : 395
% 3.41/1.59  #Fact    : 0
% 3.41/1.59  #Define  : 0
% 3.41/1.59  #Split   : 0
% 3.41/1.59  #Chain   : 0
% 3.41/1.59  #Close   : 0
% 3.41/1.59  
% 3.41/1.59  Ordering : KBO
% 3.41/1.59  
% 3.41/1.59  Simplification rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Subsume      : 20
% 3.41/1.59  #Demod        : 236
% 3.41/1.59  #Tautology    : 167
% 3.41/1.59  #SimpNegUnit  : 1
% 3.41/1.59  #BackRed      : 1
% 3.41/1.59  
% 3.41/1.59  #Partial instantiations: 0
% 3.41/1.59  #Strategies tried      : 1
% 3.41/1.59  
% 3.41/1.59  Timing (in seconds)
% 3.41/1.59  ----------------------
% 3.41/1.60  Preprocessing        : 0.28
% 3.41/1.60  Parsing              : 0.15
% 3.41/1.60  CNF conversion       : 0.02
% 3.41/1.60  Main loop            : 0.52
% 3.41/1.60  Inferencing          : 0.16
% 3.41/1.60  Reduction            : 0.24
% 3.41/1.60  Demodulation         : 0.20
% 3.41/1.60  BG Simplification    : 0.02
% 3.41/1.60  Subsumption          : 0.07
% 3.41/1.60  Abstraction          : 0.02
% 3.41/1.60  MUC search           : 0.00
% 3.41/1.60  Cooper               : 0.00
% 3.41/1.60  Total                : 0.83
% 3.41/1.60  Index Insertion      : 0.00
% 3.41/1.60  Index Deletion       : 0.00
% 3.41/1.60  Index Matching       : 0.00
% 3.41/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
