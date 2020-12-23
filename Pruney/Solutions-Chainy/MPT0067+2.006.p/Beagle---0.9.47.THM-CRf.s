%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:15 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  35 expanded)
%              Number of equality atoms :   13 (  13 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_tarski(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_33,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_55,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_37,c_55])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_92,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_92])).

tff(c_108,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16,c_104])).

tff(c_125,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_20])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.23  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.85/1.23  
% 1.85/1.23  %Foreground sorts:
% 1.85/1.23  
% 1.85/1.23  
% 1.85/1.23  %Background operators:
% 1.85/1.23  
% 1.85/1.23  
% 1.85/1.23  %Foreground operators:
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.23  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.23  
% 1.85/1.24  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.85/1.24  tff(f_53, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.85/1.24  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.85/1.24  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.85/1.24  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.85/1.24  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.85/1.24  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.85/1.24  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.24  tff(c_20, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.24  tff(c_33, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.24  tff(c_37, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_33])).
% 1.85/1.24  tff(c_55, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.85/1.24  tff(c_62, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_37, c_55])).
% 1.85/1.24  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.24  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.85/1.24  tff(c_38, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.85/1.24  tff(c_42, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_38])).
% 1.85/1.24  tff(c_92, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.24  tff(c_104, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42, c_92])).
% 1.85/1.24  tff(c_108, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16, c_104])).
% 1.85/1.24  tff(c_125, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_20])).
% 1.85/1.24  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_125])).
% 1.85/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.24  
% 1.85/1.24  Inference rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Ref     : 0
% 1.85/1.24  #Sup     : 25
% 1.85/1.24  #Fact    : 0
% 1.85/1.24  #Define  : 0
% 1.85/1.24  #Split   : 0
% 1.85/1.24  #Chain   : 0
% 1.85/1.24  #Close   : 0
% 1.85/1.24  
% 1.85/1.24  Ordering : KBO
% 1.85/1.24  
% 1.85/1.24  Simplification rules
% 1.85/1.24  ----------------------
% 1.85/1.24  #Subsume      : 1
% 1.85/1.24  #Demod        : 14
% 1.85/1.24  #Tautology    : 17
% 1.85/1.24  #SimpNegUnit  : 1
% 1.85/1.24  #BackRed      : 7
% 1.85/1.24  
% 1.85/1.24  #Partial instantiations: 0
% 1.85/1.24  #Strategies tried      : 1
% 1.85/1.24  
% 1.85/1.24  Timing (in seconds)
% 1.85/1.24  ----------------------
% 1.85/1.24  Preprocessing        : 0.31
% 1.85/1.24  Parsing              : 0.17
% 1.85/1.24  CNF conversion       : 0.02
% 1.85/1.24  Main loop            : 0.13
% 1.85/1.24  Inferencing          : 0.05
% 1.85/1.24  Reduction            : 0.04
% 1.85/1.24  Demodulation         : 0.03
% 1.85/1.24  BG Simplification    : 0.01
% 1.85/1.24  Subsumption          : 0.02
% 1.85/1.24  Abstraction          : 0.01
% 1.85/1.24  MUC search           : 0.00
% 1.85/1.24  Cooper               : 0.00
% 1.85/1.24  Total                : 0.47
% 1.85/1.24  Index Insertion      : 0.00
% 1.85/1.24  Index Deletion       : 0.00
% 1.85/1.24  Index Matching       : 0.00
% 1.85/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
