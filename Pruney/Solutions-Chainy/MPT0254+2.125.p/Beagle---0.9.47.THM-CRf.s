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
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  39 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_20])).

tff(c_162,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_162])).

tff(c_173,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [B_70] : k4_xboole_0(k1_tarski(B_70),k1_tarski(B_70)) != k1_tarski(B_70) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_189,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_50])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_16,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.22  
% 1.92/1.23  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.92/1.23  tff(f_82, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.92/1.23  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.23  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.92/1.23  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.92/1.23  tff(f_78, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.92/1.23  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.23  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.92/1.23  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.23  tff(c_117, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_20])).
% 1.92/1.23  tff(c_162, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_164, plain, (k1_tarski('#skF_1')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_162])).
% 1.92/1.23  tff(c_173, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 1.92/1.23  tff(c_16, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.23  tff(c_50, plain, (![B_70]: (k4_xboole_0(k1_tarski(B_70), k1_tarski(B_70))!=k1_tarski(B_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.92/1.23  tff(c_189, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_50])).
% 1.92/1.23  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_16, c_189])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 34
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 0
% 1.92/1.23  #Demod        : 10
% 1.92/1.23  #Tautology    : 27
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 2
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.35
% 2.04/1.23  Parsing              : 0.18
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.13
% 2.04/1.23  Inferencing          : 0.04
% 2.04/1.23  Reduction            : 0.05
% 2.04/1.23  Demodulation         : 0.04
% 2.04/1.23  BG Simplification    : 0.02
% 2.04/1.23  Subsumption          : 0.02
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.50
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
