%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  62 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_188,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_212,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_188])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_388,plain,(
    ! [B_79,A_80] : k3_tarski(k2_tarski(B_79,A_80)) = k2_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_22,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_394,plain,(
    ! [B_79,A_80] : k2_xboole_0(B_79,A_80) = k2_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_211,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_272,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_414,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_272])).

tff(c_417,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_414])).

tff(c_418,plain,(
    ! [B_81,A_82] : k2_xboole_0(B_81,A_82) = k2_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_22])).

tff(c_539,plain,(
    ! [A_86,B_87] : r1_tarski(A_86,k2_xboole_0(B_87,A_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_8])).

tff(c_557,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_539])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [B_54,C_55,A_56] :
      ( r2_hidden(B_54,C_55)
      | ~ r1_tarski(k2_tarski(A_56,B_54),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_230,plain,(
    ! [A_12,C_55] :
      ( r2_hidden(A_12,C_55)
      | ~ r1_tarski(k1_tarski(A_12),C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_576,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_557,c_230])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.57  
% 2.43/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.57  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.82/1.57  
% 2.82/1.57  %Foreground sorts:
% 2.82/1.57  
% 2.82/1.57  
% 2.82/1.57  %Background operators:
% 2.82/1.57  
% 2.82/1.57  
% 2.82/1.57  %Foreground operators:
% 2.82/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.82/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.57  
% 2.82/1.58  tff(f_64, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.82/1.58  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.82/1.58  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.82/1.58  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.82/1.58  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.82/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.82/1.58  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.82/1.58  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.82/1.58  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.82/1.58  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.58  tff(c_188, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.58  tff(c_212, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_8, c_188])).
% 2.82/1.58  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.58  tff(c_145, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.58  tff(c_388, plain, (![B_79, A_80]: (k3_tarski(k2_tarski(B_79, A_80))=k2_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 2.82/1.58  tff(c_22, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.58  tff(c_394, plain, (![B_79, A_80]: (k2_xboole_0(B_79, A_80)=k2_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_388, c_22])).
% 2.82/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.58  tff(c_34, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.82/1.58  tff(c_211, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_34, c_188])).
% 2.82/1.58  tff(c_272, plain, (k3_xboole_0('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 2.82/1.58  tff(c_414, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_272])).
% 2.82/1.58  tff(c_417, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_414])).
% 2.82/1.58  tff(c_418, plain, (![B_81, A_82]: (k2_xboole_0(B_81, A_82)=k2_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_388, c_22])).
% 2.82/1.58  tff(c_539, plain, (![A_86, B_87]: (r1_tarski(A_86, k2_xboole_0(B_87, A_86)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_8])).
% 2.82/1.58  tff(c_557, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_417, c_539])).
% 2.82/1.58  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.58  tff(c_213, plain, (![B_54, C_55, A_56]: (r2_hidden(B_54, C_55) | ~r1_tarski(k2_tarski(A_56, B_54), C_55))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.58  tff(c_230, plain, (![A_12, C_55]: (r2_hidden(A_12, C_55) | ~r1_tarski(k1_tarski(A_12), C_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_213])).
% 2.82/1.58  tff(c_576, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_557, c_230])).
% 2.82/1.58  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_576])).
% 2.82/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.58  
% 2.82/1.58  Inference rules
% 2.82/1.58  ----------------------
% 2.82/1.58  #Ref     : 0
% 2.82/1.58  #Sup     : 137
% 2.82/1.58  #Fact    : 0
% 2.82/1.58  #Define  : 0
% 2.82/1.58  #Split   : 0
% 2.82/1.58  #Chain   : 0
% 2.82/1.58  #Close   : 0
% 2.82/1.58  
% 2.82/1.58  Ordering : KBO
% 2.82/1.58  
% 2.82/1.58  Simplification rules
% 2.82/1.58  ----------------------
% 2.82/1.58  #Subsume      : 4
% 2.82/1.58  #Demod        : 32
% 2.82/1.58  #Tautology    : 73
% 2.82/1.58  #SimpNegUnit  : 1
% 2.82/1.58  #BackRed      : 3
% 2.82/1.58  
% 2.82/1.58  #Partial instantiations: 0
% 2.82/1.58  #Strategies tried      : 1
% 2.82/1.58  
% 2.82/1.58  Timing (in seconds)
% 2.82/1.58  ----------------------
% 2.82/1.58  Preprocessing        : 0.43
% 2.82/1.58  Parsing              : 0.22
% 2.82/1.58  CNF conversion       : 0.03
% 2.82/1.58  Main loop            : 0.34
% 2.82/1.58  Inferencing          : 0.12
% 2.82/1.58  Reduction            : 0.13
% 2.82/1.58  Demodulation         : 0.10
% 2.82/1.58  BG Simplification    : 0.02
% 2.82/1.58  Subsumption          : 0.05
% 2.82/1.58  Abstraction          : 0.02
% 2.82/1.58  MUC search           : 0.00
% 2.82/1.59  Cooper               : 0.00
% 2.82/1.59  Total                : 0.80
% 2.82/1.59  Index Insertion      : 0.00
% 2.82/1.59  Index Deletion       : 0.00
% 2.82/1.59  Index Matching       : 0.00
% 2.82/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
