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
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   12 (  14 expanded)
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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [B_13,A_14] :
      ( r1_xboole_0(B_13,A_14)
      | ~ r1_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    ! [B_8,A_7] : r1_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_16])).

tff(c_25,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [B_8,A_7] : k4_xboole_0(B_8,k4_xboole_0(A_7,B_8)) = B_8 ),
    inference(resolution,[status(thm)],[c_19,c_25])).

tff(c_102,plain,(
    ! [A_29,B_30] : k4_xboole_0(k4_xboole_0(A_29,B_30),B_30) = k4_xboole_0(A_29,B_30) ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [B_30,A_29] : k2_xboole_0(k4_xboole_0(B_30,k4_xboole_0(A_29,B_30)),k4_xboole_0(A_29,B_30)) = k5_xboole_0(B_30,k4_xboole_0(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_139,plain,(
    ! [B_30,A_29] : k5_xboole_0(B_30,k4_xboole_0(A_29,B_30)) = k2_xboole_0(B_30,A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32,c_114])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.68/1.11  
% 1.68/1.11  %Foreground sorts:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Background operators:
% 1.68/1.11  
% 1.68/1.11  
% 1.68/1.11  %Foreground operators:
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.11  
% 1.68/1.12  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.68/1.12  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.68/1.12  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.68/1.12  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.68/1.12  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.68/1.12  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.68/1.12  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.12  tff(c_8, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.12  tff(c_16, plain, (![B_13, A_14]: (r1_xboole_0(B_13, A_14) | ~r1_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.12  tff(c_19, plain, (![B_8, A_7]: (r1_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_16])).
% 1.68/1.12  tff(c_25, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.12  tff(c_32, plain, (![B_8, A_7]: (k4_xboole_0(B_8, k4_xboole_0(A_7, B_8))=B_8)), inference(resolution, [status(thm)], [c_19, c_25])).
% 1.68/1.12  tff(c_102, plain, (![A_29, B_30]: (k4_xboole_0(k4_xboole_0(A_29, B_30), B_30)=k4_xboole_0(A_29, B_30))), inference(resolution, [status(thm)], [c_8, c_25])).
% 1.68/1.12  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.12  tff(c_114, plain, (![B_30, A_29]: (k2_xboole_0(k4_xboole_0(B_30, k4_xboole_0(A_29, B_30)), k4_xboole_0(A_29, B_30))=k5_xboole_0(B_30, k4_xboole_0(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_2])).
% 1.68/1.12  tff(c_139, plain, (![B_30, A_29]: (k5_xboole_0(B_30, k4_xboole_0(A_29, B_30))=k2_xboole_0(B_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32, c_114])).
% 1.68/1.12  tff(c_14, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.12  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_14])).
% 1.68/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  Inference rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Ref     : 0
% 1.68/1.12  #Sup     : 34
% 1.68/1.12  #Fact    : 0
% 1.68/1.12  #Define  : 0
% 1.68/1.12  #Split   : 0
% 1.68/1.12  #Chain   : 0
% 1.68/1.12  #Close   : 0
% 1.68/1.12  
% 1.68/1.12  Ordering : KBO
% 1.68/1.12  
% 1.68/1.12  Simplification rules
% 1.68/1.12  ----------------------
% 1.68/1.12  #Subsume      : 1
% 1.68/1.12  #Demod        : 22
% 1.68/1.12  #Tautology    : 22
% 1.68/1.12  #SimpNegUnit  : 0
% 1.68/1.12  #BackRed      : 1
% 1.68/1.12  
% 1.68/1.12  #Partial instantiations: 0
% 1.68/1.12  #Strategies tried      : 1
% 1.68/1.12  
% 1.68/1.12  Timing (in seconds)
% 1.68/1.12  ----------------------
% 1.68/1.12  Preprocessing        : 0.25
% 1.68/1.12  Parsing              : 0.14
% 1.68/1.12  CNF conversion       : 0.01
% 1.68/1.13  Main loop            : 0.13
% 1.68/1.13  Inferencing          : 0.06
% 1.68/1.13  Reduction            : 0.04
% 1.68/1.13  Demodulation         : 0.03
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.02
% 1.68/1.13  Abstraction          : 0.01
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.40
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
