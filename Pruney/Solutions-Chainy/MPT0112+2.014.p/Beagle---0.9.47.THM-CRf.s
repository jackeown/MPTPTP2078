%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:10 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :   12 (  15 expanded)
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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ r2_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_31])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_35,c_8])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_68,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_65])).

tff(c_72,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.10  
% 1.60/1.10  %Foreground sorts:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Background operators:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Foreground operators:
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.10  
% 1.60/1.11  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.60/1.11  tff(f_46, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.60/1.11  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.60/1.11  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.60/1.11  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.60/1.11  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.11  tff(c_16, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.60/1.11  tff(c_31, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~r2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.11  tff(c_35, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_31])).
% 1.60/1.11  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.60/1.11  tff(c_40, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_35, c_8])).
% 1.60/1.11  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.11  tff(c_14, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.60/1.11  tff(c_56, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.11  tff(c_65, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_56])).
% 1.60/1.11  tff(c_68, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_65])).
% 1.60/1.11  tff(c_72, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16])).
% 1.60/1.11  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_72])).
% 1.60/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  Inference rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Ref     : 0
% 1.60/1.11  #Sup     : 13
% 1.60/1.11  #Fact    : 0
% 1.60/1.11  #Define  : 0
% 1.60/1.11  #Split   : 0
% 1.60/1.11  #Chain   : 0
% 1.60/1.11  #Close   : 0
% 1.60/1.11  
% 1.60/1.11  Ordering : KBO
% 1.60/1.11  
% 1.60/1.11  Simplification rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Subsume      : 0
% 1.60/1.11  #Demod        : 7
% 1.60/1.11  #Tautology    : 10
% 1.60/1.11  #SimpNegUnit  : 1
% 1.60/1.11  #BackRed      : 4
% 1.60/1.11  
% 1.60/1.11  #Partial instantiations: 0
% 1.60/1.11  #Strategies tried      : 1
% 1.60/1.11  
% 1.60/1.11  Timing (in seconds)
% 1.60/1.11  ----------------------
% 1.60/1.11  Preprocessing        : 0.25
% 1.60/1.11  Parsing              : 0.14
% 1.60/1.11  CNF conversion       : 0.01
% 1.60/1.11  Main loop            : 0.10
% 1.60/1.11  Inferencing          : 0.05
% 1.60/1.11  Reduction            : 0.03
% 1.60/1.11  Demodulation         : 0.02
% 1.60/1.11  BG Simplification    : 0.01
% 1.60/1.11  Subsumption          : 0.01
% 1.60/1.11  Abstraction          : 0.00
% 1.60/1.11  MUC search           : 0.00
% 1.60/1.11  Cooper               : 0.00
% 1.60/1.11  Total                : 0.37
% 1.60/1.12  Index Insertion      : 0.00
% 1.60/1.12  Index Deletion       : 0.00
% 1.60/1.12  Index Matching       : 0.00
% 1.60/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
