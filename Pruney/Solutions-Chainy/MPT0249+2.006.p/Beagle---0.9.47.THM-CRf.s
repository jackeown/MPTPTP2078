%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   40 (  79 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 135 expanded)
%              Number of equality atoms :   26 (  87 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [B_17] : r1_tarski(k1_tarski(B_17),k1_tarski(B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_165,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(k2_xboole_0(A_41,B_43),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [C_44] :
      ( r1_tarski('#skF_2',C_44)
      | ~ r1_tarski(k1_tarski('#skF_1'),C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_165])).

tff(c_196,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_181])).

tff(c_225,plain,(
    ! [B_48,A_49] :
      ( k1_tarski(B_48) = A_49
      | k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k1_tarski(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_228,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_196,c_225])).

tff(c_237,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_228])).

tff(c_58,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_38])).

tff(c_209,plain,(
    ! [C_47] :
      ( r1_tarski('#skF_3',C_47)
      | ~ r1_tarski(k1_tarski('#skF_1'),C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_165])).

tff(c_224,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_304,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_224])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(B_17) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_250,plain,(
    ! [A_16] :
      ( k1_tarski('#skF_1') = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_14])).

tff(c_353,plain,(
    ! [A_56] :
      ( A_56 = '#skF_2'
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_250])).

tff(c_356,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_304,c_353])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_36,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.29  
% 2.28/1.29  %Foreground sorts:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Background operators:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Foreground operators:
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.29  
% 2.28/1.30  tff(f_75, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.28/1.30  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.28/1.30  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.28/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.28/1.30  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.30  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.30  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.30  tff(c_16, plain, (![B_17]: (r1_tarski(k1_tarski(B_17), k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.30  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.30  tff(c_165, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(k2_xboole_0(A_41, B_43), C_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.30  tff(c_181, plain, (![C_44]: (r1_tarski('#skF_2', C_44) | ~r1_tarski(k1_tarski('#skF_1'), C_44))), inference(superposition, [status(thm), theory('equality')], [c_38, c_165])).
% 2.28/1.30  tff(c_196, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_181])).
% 2.28/1.30  tff(c_225, plain, (![B_48, A_49]: (k1_tarski(B_48)=A_49 | k1_xboole_0=A_49 | ~r1_tarski(A_49, k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.30  tff(c_228, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_196, c_225])).
% 2.28/1.30  tff(c_237, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_228])).
% 2.28/1.30  tff(c_58, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.30  tff(c_73, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_58, c_38])).
% 2.28/1.30  tff(c_209, plain, (![C_47]: (r1_tarski('#skF_3', C_47) | ~r1_tarski(k1_tarski('#skF_1'), C_47))), inference(superposition, [status(thm), theory('equality')], [c_73, c_165])).
% 2.28/1.30  tff(c_224, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_209])).
% 2.28/1.30  tff(c_304, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_224])).
% 2.28/1.30  tff(c_14, plain, (![B_17, A_16]: (k1_tarski(B_17)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.30  tff(c_250, plain, (![A_16]: (k1_tarski('#skF_1')=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_14])).
% 2.28/1.30  tff(c_353, plain, (![A_56]: (A_56='#skF_2' | k1_xboole_0=A_56 | ~r1_tarski(A_56, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_250])).
% 2.28/1.30  tff(c_356, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_304, c_353])).
% 2.28/1.30  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_36, c_356])).
% 2.28/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  Inference rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Ref     : 0
% 2.28/1.30  #Sup     : 80
% 2.28/1.30  #Fact    : 0
% 2.28/1.30  #Define  : 0
% 2.28/1.30  #Split   : 0
% 2.28/1.30  #Chain   : 0
% 2.28/1.30  #Close   : 0
% 2.28/1.30  
% 2.28/1.30  Ordering : KBO
% 2.28/1.30  
% 2.28/1.30  Simplification rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Subsume      : 3
% 2.28/1.30  #Demod        : 36
% 2.28/1.30  #Tautology    : 57
% 2.28/1.30  #SimpNegUnit  : 2
% 2.28/1.30  #BackRed      : 4
% 2.28/1.30  
% 2.28/1.30  #Partial instantiations: 0
% 2.28/1.30  #Strategies tried      : 1
% 2.28/1.30  
% 2.28/1.30  Timing (in seconds)
% 2.28/1.30  ----------------------
% 2.28/1.30  Preprocessing        : 0.32
% 2.28/1.30  Parsing              : 0.17
% 2.28/1.30  CNF conversion       : 0.02
% 2.28/1.30  Main loop            : 0.22
% 2.28/1.30  Inferencing          : 0.08
% 2.28/1.30  Reduction            : 0.09
% 2.28/1.30  Demodulation         : 0.07
% 2.28/1.30  BG Simplification    : 0.01
% 2.28/1.30  Subsumption          : 0.03
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.56
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
