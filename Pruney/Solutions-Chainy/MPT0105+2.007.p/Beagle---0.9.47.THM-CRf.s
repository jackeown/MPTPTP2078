%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  23 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_93,plain,(
    ! [A_23,B_24] : k2_xboole_0(k4_xboole_0(A_23,B_24),k4_xboole_0(B_24,A_23)) = k5_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [B_27,A_28] : k2_xboole_0(k4_xboole_0(B_27,A_28),k4_xboole_0(A_28,B_27)) = k5_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_155,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(B_8,k4_xboole_0(A_7,B_8))) = k5_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_134])).

tff(c_169,plain,(
    ! [B_8,A_7] : k5_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = k2_xboole_0(B_8,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_6,c_155])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:18:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.91/1.24  
% 1.91/1.24  %Foreground sorts:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Background operators:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Foreground operators:
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.24  
% 1.91/1.25  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.91/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.91/1.25  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.91/1.25  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.25  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.91/1.25  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.91/1.25  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.25  tff(c_8, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.25  tff(c_50, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.25  tff(c_58, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_8, c_50])).
% 1.91/1.25  tff(c_93, plain, (![A_23, B_24]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k4_xboole_0(B_24, A_23))=k5_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.25  tff(c_134, plain, (![B_27, A_28]: (k2_xboole_0(k4_xboole_0(B_27, A_28), k4_xboole_0(A_28, B_27))=k5_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 1.91/1.25  tff(c_155, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k4_xboole_0(B_8, k4_xboole_0(A_7, B_8)))=k5_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_134])).
% 1.91/1.25  tff(c_169, plain, (![B_8, A_7]: (k5_xboole_0(B_8, k4_xboole_0(A_7, B_8))=k2_xboole_0(B_8, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_6, c_155])).
% 1.91/1.25  tff(c_14, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.25  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_14])).
% 1.91/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  Inference rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Ref     : 0
% 1.91/1.25  #Sup     : 51
% 1.91/1.25  #Fact    : 0
% 1.91/1.25  #Define  : 0
% 1.91/1.25  #Split   : 0
% 1.91/1.25  #Chain   : 0
% 1.91/1.25  #Close   : 0
% 1.91/1.25  
% 1.91/1.25  Ordering : KBO
% 1.91/1.25  
% 1.91/1.25  Simplification rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Subsume      : 1
% 1.91/1.25  #Demod        : 21
% 1.91/1.25  #Tautology    : 36
% 1.91/1.25  #SimpNegUnit  : 0
% 1.91/1.25  #BackRed      : 1
% 1.91/1.25  
% 1.91/1.25  #Partial instantiations: 0
% 1.91/1.25  #Strategies tried      : 1
% 1.91/1.25  
% 1.91/1.25  Timing (in seconds)
% 1.91/1.25  ----------------------
% 1.91/1.25  Preprocessing        : 0.32
% 1.91/1.25  Parsing              : 0.16
% 1.91/1.25  CNF conversion       : 0.02
% 1.91/1.25  Main loop            : 0.17
% 1.91/1.25  Inferencing          : 0.06
% 1.91/1.25  Reduction            : 0.06
% 1.91/1.25  Demodulation         : 0.06
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.03
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.51
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
