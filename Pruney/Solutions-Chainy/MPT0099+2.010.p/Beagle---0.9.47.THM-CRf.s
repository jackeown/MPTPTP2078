%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:37 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
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

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_43,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),k4_xboole_0(B_19,A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ r1_xboole_0(A_8,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [B_19] : k4_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_12])).

tff(c_138,plain,(
    ! [A_26,B_27] : k2_xboole_0(k4_xboole_0(A_26,B_27),k4_xboole_0(B_27,A_26)) = k5_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,(
    ! [B_27] : k5_xboole_0(B_27,B_27) = k4_xboole_0(B_27,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_4])).

tff(c_166,plain,(
    ! [B_27] : k5_xboole_0(B_27,B_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_145])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  
% 1.78/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.14  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.78/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.14  
% 1.78/1.15  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 1.78/1.15  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.78/1.15  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.78/1.15  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.78/1.15  tff(f_58, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.78/1.15  tff(c_43, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), k4_xboole_0(B_19, A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.15  tff(c_12, plain, (![A_8]: (~r1_xboole_0(A_8, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.15  tff(c_54, plain, (![B_19]: (k4_xboole_0(B_19, B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_43, c_12])).
% 1.78/1.15  tff(c_138, plain, (![A_26, B_27]: (k2_xboole_0(k4_xboole_0(A_26, B_27), k4_xboole_0(B_27, A_26))=k5_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.15  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.15  tff(c_145, plain, (![B_27]: (k5_xboole_0(B_27, B_27)=k4_xboole_0(B_27, B_27))), inference(superposition, [status(thm), theory('equality')], [c_138, c_4])).
% 1.78/1.15  tff(c_166, plain, (![B_27]: (k5_xboole_0(B_27, B_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_145])).
% 1.78/1.15  tff(c_18, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.15  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_18])).
% 1.78/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  Inference rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Ref     : 0
% 1.78/1.15  #Sup     : 34
% 1.78/1.15  #Fact    : 0
% 1.78/1.15  #Define  : 0
% 1.78/1.15  #Split   : 0
% 1.78/1.15  #Chain   : 0
% 1.78/1.15  #Close   : 0
% 1.78/1.15  
% 1.78/1.15  Ordering : KBO
% 1.78/1.15  
% 1.78/1.15  Simplification rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Subsume      : 0
% 1.78/1.15  #Demod        : 18
% 1.78/1.15  #Tautology    : 24
% 1.78/1.15  #SimpNegUnit  : 0
% 1.78/1.15  #BackRed      : 1
% 1.78/1.15  
% 1.78/1.15  #Partial instantiations: 0
% 1.78/1.15  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.27
% 1.78/1.15  Parsing              : 0.15
% 1.78/1.15  CNF conversion       : 0.02
% 1.78/1.15  Main loop            : 0.12
% 1.78/1.15  Inferencing          : 0.05
% 1.78/1.15  Reduction            : 0.04
% 1.78/1.15  Demodulation         : 0.03
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.02
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.41
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
