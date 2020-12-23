%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 ( 109 expanded)
%              Number of equality atoms :   32 (  86 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    ! [B_25,A_26] : k3_tarski(k2_tarski(B_25,A_26)) = k2_xboole_0(A_26,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_16,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_216,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_16])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_155,plain,(
    ! [B_27,A_28] :
      ( k1_tarski(B_27) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_169,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_161])).

tff(c_173,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_24])).

tff(c_231,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_173])).

tff(c_271,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_2])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    ! [A_8] :
      ( k1_tarski('#skF_1') = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_10])).

tff(c_304,plain,(
    ! [A_33] :
      ( A_33 = '#skF_2'
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_177])).

tff(c_307,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_271,c_304])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_22,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.27  
% 1.92/1.27  %Foreground sorts:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Background operators:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Foreground operators:
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.27  
% 2.04/1.28  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.04/1.28  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.04/1.28  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.04/1.28  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.04/1.28  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.04/1.28  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_22, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.28  tff(c_86, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.28  tff(c_129, plain, (![B_25, A_26]: (k3_tarski(k2_tarski(B_25, A_26))=k2_xboole_0(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_4, c_86])).
% 2.04/1.28  tff(c_16, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.28  tff(c_216, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_129, c_16])).
% 2.04/1.28  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_24, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.28  tff(c_30, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2])).
% 2.04/1.28  tff(c_155, plain, (![B_27, A_28]: (k1_tarski(B_27)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.28  tff(c_161, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_155])).
% 2.04/1.28  tff(c_169, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_20, c_161])).
% 2.04/1.28  tff(c_173, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_24])).
% 2.04/1.28  tff(c_231, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_216, c_173])).
% 2.04/1.28  tff(c_271, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_2])).
% 2.04/1.28  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.28  tff(c_177, plain, (![A_8]: (k1_tarski('#skF_1')=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_10])).
% 2.04/1.28  tff(c_304, plain, (![A_33]: (A_33='#skF_2' | k1_xboole_0=A_33 | ~r1_tarski(A_33, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_177])).
% 2.04/1.28  tff(c_307, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_271, c_304])).
% 2.04/1.28  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_22, c_307])).
% 2.04/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  Inference rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Ref     : 0
% 2.04/1.28  #Sup     : 76
% 2.04/1.28  #Fact    : 0
% 2.04/1.28  #Define  : 0
% 2.04/1.28  #Split   : 0
% 2.04/1.28  #Chain   : 0
% 2.04/1.28  #Close   : 0
% 2.04/1.28  
% 2.04/1.28  Ordering : KBO
% 2.04/1.28  
% 2.04/1.28  Simplification rules
% 2.04/1.28  ----------------------
% 2.04/1.28  #Subsume      : 2
% 2.04/1.28  #Demod        : 23
% 2.04/1.28  #Tautology    : 58
% 2.04/1.28  #SimpNegUnit  : 2
% 2.04/1.28  #BackRed      : 2
% 2.04/1.28  
% 2.04/1.28  #Partial instantiations: 0
% 2.04/1.28  #Strategies tried      : 1
% 2.04/1.28  
% 2.04/1.28  Timing (in seconds)
% 2.04/1.28  ----------------------
% 2.04/1.28  Preprocessing        : 0.29
% 2.04/1.28  Parsing              : 0.16
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.17
% 2.04/1.28  Inferencing          : 0.06
% 2.04/1.28  Reduction            : 0.07
% 2.04/1.28  Demodulation         : 0.05
% 2.04/1.28  BG Simplification    : 0.01
% 2.04/1.28  Subsumption          : 0.02
% 2.04/1.28  Abstraction          : 0.01
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.49
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
