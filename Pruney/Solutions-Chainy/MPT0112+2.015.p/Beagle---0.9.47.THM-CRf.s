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
% DateTime   : Thu Dec  3 09:45:10 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  30 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_29])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,
    ( k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_58,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_8,c_54])).

tff(c_61,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:13:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.10  
% 1.63/1.10  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.63/1.10  tff(f_44, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.63/1.10  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.63/1.10  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.63/1.10  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.10  tff(c_14, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.10  tff(c_29, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.10  tff(c_33, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_29])).
% 1.63/1.10  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.10  tff(c_12, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.10  tff(c_45, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.63/1.10  tff(c_54, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_45])).
% 1.63/1.10  tff(c_58, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_8, c_54])).
% 1.63/1.10  tff(c_61, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14])).
% 1.63/1.10  tff(c_63, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_61])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 10
% 1.63/1.10  #Fact    : 0
% 1.63/1.10  #Define  : 0
% 1.63/1.10  #Split   : 0
% 1.63/1.10  #Chain   : 0
% 1.63/1.10  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 0
% 1.63/1.11  #Demod        : 5
% 1.63/1.11  #Tautology    : 8
% 1.63/1.11  #SimpNegUnit  : 1
% 1.63/1.11  #BackRed      : 3
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.26
% 1.63/1.11  Parsing              : 0.15
% 1.63/1.11  CNF conversion       : 0.02
% 1.63/1.11  Main loop            : 0.09
% 1.63/1.11  Inferencing          : 0.04
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.01
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.37
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
