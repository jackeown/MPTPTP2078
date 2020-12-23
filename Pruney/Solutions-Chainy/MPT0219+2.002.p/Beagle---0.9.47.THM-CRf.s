%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),k1_tarski(B_32)) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_35,plain,(
    ! [B_21,A_22] : k2_tarski(B_21,A_22) = k2_tarski(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k1_tarski(A_13),k2_tarski(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_22,B_21] : r1_tarski(k1_tarski(A_22),k2_tarski(B_21,A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_14])).

tff(c_134,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_50])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(k1_tarski(A_15),k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_134,c_16])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:42:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.15  
% 1.69/1.16  tff(f_48, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.69/1.16  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.69/1.16  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.69/1.16  tff(f_39, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.69/1.16  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.69/1.16  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.69/1.16  tff(c_116, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(B_32))=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.16  tff(c_20, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.69/1.16  tff(c_122, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_116, c_20])).
% 1.69/1.16  tff(c_35, plain, (![B_21, A_22]: (k2_tarski(B_21, A_22)=k2_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.16  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), k2_tarski(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.16  tff(c_50, plain, (![A_22, B_21]: (r1_tarski(k1_tarski(A_22), k2_tarski(B_21, A_22)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_14])).
% 1.69/1.16  tff(c_134, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_50])).
% 1.69/1.16  tff(c_16, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(k1_tarski(A_15), k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.16  tff(c_145, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_134, c_16])).
% 1.69/1.16  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_145])).
% 1.69/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  Inference rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Ref     : 0
% 1.69/1.16  #Sup     : 32
% 1.69/1.16  #Fact    : 0
% 1.69/1.16  #Define  : 0
% 1.69/1.16  #Split   : 0
% 1.69/1.16  #Chain   : 0
% 1.69/1.16  #Close   : 0
% 1.69/1.16  
% 1.69/1.16  Ordering : KBO
% 1.69/1.16  
% 1.69/1.16  Simplification rules
% 1.69/1.16  ----------------------
% 1.69/1.16  #Subsume      : 0
% 1.69/1.16  #Demod        : 6
% 1.69/1.16  #Tautology    : 27
% 1.69/1.16  #SimpNegUnit  : 1
% 1.69/1.16  #BackRed      : 0
% 1.69/1.16  
% 1.69/1.16  #Partial instantiations: 0
% 1.69/1.16  #Strategies tried      : 1
% 1.69/1.16  
% 1.69/1.16  Timing (in seconds)
% 1.69/1.16  ----------------------
% 1.69/1.16  Preprocessing        : 0.29
% 1.69/1.16  Parsing              : 0.15
% 1.69/1.16  CNF conversion       : 0.02
% 1.69/1.16  Main loop            : 0.12
% 1.69/1.16  Inferencing          : 0.05
% 1.69/1.16  Reduction            : 0.04
% 1.69/1.16  Demodulation         : 0.03
% 1.69/1.16  BG Simplification    : 0.01
% 1.69/1.16  Subsumption          : 0.02
% 1.69/1.16  Abstraction          : 0.01
% 1.69/1.16  MUC search           : 0.00
% 1.69/1.16  Cooper               : 0.00
% 1.69/1.16  Total                : 0.43
% 1.69/1.16  Index Insertion      : 0.00
% 1.69/1.16  Index Deletion       : 0.00
% 1.69/1.16  Index Matching       : 0.00
% 1.69/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
