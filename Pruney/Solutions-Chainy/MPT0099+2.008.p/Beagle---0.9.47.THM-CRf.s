%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_51,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),k4_xboole_0(B_17,A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_10])).

tff(c_72,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k4_xboole_0(B_20,A_19)) = k5_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k4_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_94,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_79])).

tff(c_16,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.09  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.60/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.09  
% 1.60/1.10  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 1.60/1.10  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.60/1.10  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.60/1.10  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.60/1.10  tff(f_56, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.60/1.10  tff(c_51, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), k4_xboole_0(B_17, A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.60/1.10  tff(c_10, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.10  tff(c_56, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_10])).
% 1.60/1.10  tff(c_72, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k4_xboole_0(B_20, A_19))=k5_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.10  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.10  tff(c_79, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k4_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 1.60/1.10  tff(c_94, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_79])).
% 1.60/1.10  tff(c_16, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.60/1.10  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_16])).
% 1.60/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  Inference rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Ref     : 0
% 1.60/1.10  #Sup     : 18
% 1.60/1.10  #Fact    : 0
% 1.60/1.10  #Define  : 0
% 1.60/1.10  #Split   : 0
% 1.60/1.10  #Chain   : 0
% 1.60/1.10  #Close   : 0
% 1.60/1.10  
% 1.60/1.10  Ordering : KBO
% 1.60/1.10  
% 1.60/1.10  Simplification rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Subsume      : 0
% 1.60/1.10  #Demod        : 11
% 1.60/1.10  #Tautology    : 13
% 1.60/1.10  #SimpNegUnit  : 0
% 1.60/1.10  #BackRed      : 1
% 1.60/1.10  
% 1.60/1.10  #Partial instantiations: 0
% 1.60/1.10  #Strategies tried      : 1
% 1.60/1.10  
% 1.60/1.10  Timing (in seconds)
% 1.60/1.10  ----------------------
% 1.60/1.10  Preprocessing        : 0.26
% 1.60/1.11  Parsing              : 0.14
% 1.60/1.11  CNF conversion       : 0.01
% 1.60/1.11  Main loop            : 0.08
% 1.60/1.11  Inferencing          : 0.04
% 1.60/1.11  Reduction            : 0.03
% 1.60/1.11  Demodulation         : 0.02
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.00
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.36
% 1.60/1.11  Index Insertion      : 0.00
% 1.60/1.11  Index Deletion       : 0.00
% 1.60/1.11  Index Matching       : 0.00
% 1.60/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
