%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k1_tarski(A_15),k2_tarski(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k2_tarski(A_15,B_16)) = k2_tarski(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(k2_tarski(A_41,B_42),k1_tarski(B_42)) = k1_tarski(A_41)
      | B_42 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_306,plain,(
    ! [B_49,A_50] :
      ( k4_xboole_0(k2_tarski(B_49,A_50),k1_tarski(B_49)) = k1_tarski(A_50)
      | B_49 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_168])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_316,plain,(
    ! [B_49,A_50] :
      ( k5_xboole_0(k1_tarski(B_49),k1_tarski(A_50)) = k2_xboole_0(k1_tarski(B_49),k2_tarski(B_49,A_50))
      | B_49 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_6])).

tff(c_339,plain,(
    ! [B_51,A_52] :
      ( k5_xboole_0(k1_tarski(B_51),k1_tarski(A_52)) = k2_tarski(B_51,A_52)
      | B_51 = A_52 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_316])).

tff(c_20,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_345,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_20])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.67  
% 2.43/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.67  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.43/1.67  
% 2.43/1.67  %Foreground sorts:
% 2.43/1.67  
% 2.43/1.67  
% 2.43/1.67  %Background operators:
% 2.43/1.67  
% 2.43/1.67  
% 2.43/1.67  %Foreground operators:
% 2.43/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.67  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.67  
% 2.58/1.68  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.58/1.68  tff(f_43, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.58/1.68  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.58/1.68  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.58/1.68  tff(f_48, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.58/1.68  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.58/1.68  tff(c_22, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.68  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), k2_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.68  tff(c_76, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.68  tff(c_84, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(A_15, B_16))=k2_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_76])).
% 2.58/1.68  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.68  tff(c_168, plain, (![A_41, B_42]: (k4_xboole_0(k2_tarski(A_41, B_42), k1_tarski(B_42))=k1_tarski(A_41) | B_42=A_41)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.58/1.68  tff(c_306, plain, (![B_49, A_50]: (k4_xboole_0(k2_tarski(B_49, A_50), k1_tarski(B_49))=k1_tarski(A_50) | B_49=A_50)), inference(superposition, [status(thm), theory('equality')], [c_8, c_168])).
% 2.58/1.68  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.68  tff(c_316, plain, (![B_49, A_50]: (k5_xboole_0(k1_tarski(B_49), k1_tarski(A_50))=k2_xboole_0(k1_tarski(B_49), k2_tarski(B_49, A_50)) | B_49=A_50)), inference(superposition, [status(thm), theory('equality')], [c_306, c_6])).
% 2.58/1.68  tff(c_339, plain, (![B_51, A_52]: (k5_xboole_0(k1_tarski(B_51), k1_tarski(A_52))=k2_tarski(B_51, A_52) | B_51=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_316])).
% 2.58/1.68  tff(c_20, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.68  tff(c_345, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_339, c_20])).
% 2.58/1.68  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_345])).
% 2.58/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.68  
% 2.58/1.68  Inference rules
% 2.58/1.68  ----------------------
% 2.58/1.68  #Ref     : 0
% 2.58/1.68  #Sup     : 78
% 2.58/1.68  #Fact    : 0
% 2.58/1.68  #Define  : 0
% 2.58/1.68  #Split   : 0
% 2.58/1.68  #Chain   : 0
% 2.58/1.68  #Close   : 0
% 2.58/1.68  
% 2.58/1.68  Ordering : KBO
% 2.58/1.68  
% 2.58/1.68  Simplification rules
% 2.58/1.68  ----------------------
% 2.58/1.68  #Subsume      : 7
% 2.58/1.68  #Demod        : 35
% 2.58/1.69  #Tautology    : 59
% 2.58/1.69  #SimpNegUnit  : 1
% 2.58/1.69  #BackRed      : 0
% 2.58/1.69  
% 2.58/1.69  #Partial instantiations: 0
% 2.58/1.69  #Strategies tried      : 1
% 2.58/1.69  
% 2.58/1.69  Timing (in seconds)
% 2.58/1.69  ----------------------
% 2.58/1.69  Preprocessing        : 0.46
% 2.58/1.69  Parsing              : 0.24
% 2.58/1.69  CNF conversion       : 0.03
% 2.58/1.69  Main loop            : 0.31
% 2.58/1.69  Inferencing          : 0.12
% 2.58/1.69  Reduction            : 0.11
% 2.58/1.69  Demodulation         : 0.08
% 2.58/1.69  BG Simplification    : 0.02
% 2.58/1.69  Subsumption          : 0.04
% 2.58/1.69  Abstraction          : 0.02
% 2.58/1.69  MUC search           : 0.00
% 2.58/1.69  Cooper               : 0.00
% 2.58/1.69  Total                : 0.81
% 2.58/1.69  Index Insertion      : 0.00
% 2.58/1.69  Index Deletion       : 0.00
% 2.58/1.69  Index Matching       : 0.00
% 2.58/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
