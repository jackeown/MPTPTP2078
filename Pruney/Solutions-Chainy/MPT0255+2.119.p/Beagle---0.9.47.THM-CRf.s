%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:54 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_141,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),B_23) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_153,plain,(
    ! [A_42,B_43] : k2_tarski(A_42,B_43) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_26])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_110,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_110])).

tff(c_124,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_114])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.18  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.18  
% 1.78/1.18  %Foreground sorts:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Background operators:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Foreground operators:
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.78/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.78/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.18  
% 1.78/1.18  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.78/1.18  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.78/1.18  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.78/1.18  tff(f_56, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.78/1.18  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.78/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.18  tff(c_141, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.78/1.18  tff(c_26, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.18  tff(c_153, plain, (![A_42, B_43]: (k2_tarski(A_42, B_43)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_26])).
% 1.78/1.18  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.18  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.18  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.18  tff(c_46, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_10])).
% 1.78/1.18  tff(c_110, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.18  tff(c_114, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_110])).
% 1.78/1.18  tff(c_124, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_114])).
% 1.78/1.18  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_124])).
% 1.78/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  Inference rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Ref     : 0
% 1.78/1.18  #Sup     : 33
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 0
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 0
% 1.78/1.19  #Demod        : 9
% 1.78/1.19  #Tautology    : 22
% 1.78/1.19  #SimpNegUnit  : 1
% 1.78/1.19  #BackRed      : 3
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.78/1.19  Preprocessing        : 0.30
% 1.78/1.19  Parsing              : 0.16
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.13
% 1.78/1.19  Inferencing          : 0.05
% 1.78/1.19  Reduction            : 0.05
% 1.78/1.19  Demodulation         : 0.04
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.02
% 1.78/1.19  Abstraction          : 0.01
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.45
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
