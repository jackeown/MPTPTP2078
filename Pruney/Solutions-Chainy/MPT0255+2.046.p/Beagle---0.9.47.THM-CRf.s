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
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   49 (  91 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 ( 106 expanded)
%              Number of equality atoms :   23 (  49 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_55,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_28])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_416,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_420,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_416])).

tff(c_434,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_420])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_208,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [B_46] : k2_xboole_0(B_46,B_46) = B_46 ),
    inference(resolution,[status(thm)],[c_8,c_208])).

tff(c_26,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    ! [B_31,A_20] : k2_xboole_0(B_31,k1_tarski(A_20)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_249,plain,(
    ! [A_20] : k1_tarski(A_20) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_77])).

tff(c_448,plain,(
    ! [A_20] : k1_tarski(A_20) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_249])).

tff(c_455,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_12])).

tff(c_46,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_424,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_416])).

tff(c_438,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_424])).

tff(c_493,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_438])).

tff(c_24,plain,(
    ! [A_18,B_19] : r1_tarski(k1_tarski(A_18),k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_502,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_24])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_617,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_502,c_4])).

tff(c_623,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_617])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.25  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.25  
% 1.94/1.25  %Foreground sorts:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Background operators:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Foreground operators:
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.25  
% 1.94/1.26  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.94/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.94/1.26  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.94/1.26  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.94/1.26  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.94/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.94/1.26  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.94/1.26  tff(f_51, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.94/1.26  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.26  tff(c_55, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.26  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_70, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_55, c_28])).
% 1.94/1.26  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.26  tff(c_117, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_14])).
% 1.94/1.26  tff(c_416, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.26  tff(c_420, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_117, c_416])).
% 1.94/1.26  tff(c_434, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_420])).
% 1.94/1.26  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.26  tff(c_208, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.26  tff(c_242, plain, (![B_46]: (k2_xboole_0(B_46, B_46)=B_46)), inference(resolution, [status(thm)], [c_8, c_208])).
% 1.94/1.26  tff(c_26, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.26  tff(c_77, plain, (![B_31, A_20]: (k2_xboole_0(B_31, k1_tarski(A_20))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_26])).
% 1.94/1.26  tff(c_249, plain, (![A_20]: (k1_tarski(A_20)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242, c_77])).
% 1.94/1.26  tff(c_448, plain, (![A_20]: (k1_tarski(A_20)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_249])).
% 1.94/1.26  tff(c_455, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_12])).
% 1.94/1.26  tff(c_46, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_14])).
% 1.94/1.26  tff(c_424, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_416])).
% 1.94/1.26  tff(c_438, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_424])).
% 1.94/1.26  tff(c_493, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_438])).
% 1.94/1.26  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.26  tff(c_502, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_493, c_24])).
% 1.94/1.26  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.26  tff(c_617, plain, (k1_tarski('#skF_1')='#skF_3' | ~r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_502, c_4])).
% 1.94/1.26  tff(c_623, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_617])).
% 1.94/1.26  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_448, c_623])).
% 1.94/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  Inference rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Ref     : 0
% 1.94/1.26  #Sup     : 144
% 1.94/1.26  #Fact    : 0
% 1.94/1.26  #Define  : 0
% 1.94/1.26  #Split   : 0
% 1.94/1.26  #Chain   : 0
% 1.94/1.26  #Close   : 0
% 1.94/1.26  
% 1.94/1.26  Ordering : KBO
% 1.94/1.26  
% 1.94/1.26  Simplification rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Subsume      : 10
% 1.94/1.26  #Demod        : 68
% 1.94/1.26  #Tautology    : 97
% 1.94/1.26  #SimpNegUnit  : 1
% 1.94/1.26  #BackRed      : 15
% 1.94/1.26  
% 1.94/1.26  #Partial instantiations: 0
% 1.94/1.26  #Strategies tried      : 1
% 1.94/1.26  
% 1.94/1.26  Timing (in seconds)
% 1.94/1.26  ----------------------
% 1.94/1.26  Preprocessing        : 0.28
% 1.94/1.26  Parsing              : 0.15
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.24
% 1.94/1.26  Inferencing          : 0.08
% 1.94/1.26  Reduction            : 0.09
% 1.94/1.26  Demodulation         : 0.07
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.04
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.55
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
