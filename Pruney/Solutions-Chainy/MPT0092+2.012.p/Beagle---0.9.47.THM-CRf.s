%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:30 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_31])).

tff(c_70,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_70])).

tff(c_82,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | k4_xboole_0(A_25,B_24) != A_25 ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_1') != k4_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_90,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_1')) != k4_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.51  
% 2.11/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.51  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.51  
% 2.11/1.51  %Foreground sorts:
% 2.11/1.51  
% 2.11/1.51  
% 2.11/1.51  %Background operators:
% 2.11/1.51  
% 2.11/1.51  
% 2.11/1.51  %Foreground operators:
% 2.11/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.51  
% 2.11/1.53  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.53  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.11/1.53  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.11/1.53  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.11/1.53  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.11/1.53  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.11/1.53  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.53  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.53  tff(c_31, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.53  tff(c_35, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_31])).
% 2.11/1.53  tff(c_70, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.53  tff(c_79, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35, c_70])).
% 2.11/1.53  tff(c_82, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_79])).
% 2.11/1.53  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.53  tff(c_36, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.53  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.53  tff(c_58, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | k4_xboole_0(A_25, B_24)!=A_25)), inference(resolution, [status(thm)], [c_36, c_2])).
% 2.11/1.53  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.53  tff(c_69, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_1')!=k4_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_18])).
% 2.11/1.53  tff(c_90, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_1'))!=k4_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_69])).
% 2.11/1.53  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_90])).
% 2.11/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.53  
% 2.11/1.53  Inference rules
% 2.11/1.53  ----------------------
% 2.11/1.53  #Ref     : 0
% 2.11/1.53  #Sup     : 18
% 2.11/1.53  #Fact    : 0
% 2.11/1.53  #Define  : 0
% 2.11/1.53  #Split   : 0
% 2.11/1.53  #Chain   : 0
% 2.18/1.53  #Close   : 0
% 2.18/1.53  
% 2.18/1.53  Ordering : KBO
% 2.18/1.53  
% 2.18/1.53  Simplification rules
% 2.18/1.53  ----------------------
% 2.18/1.53  #Subsume      : 1
% 2.18/1.53  #Demod        : 3
% 2.18/1.53  #Tautology    : 10
% 2.18/1.53  #SimpNegUnit  : 0
% 2.18/1.53  #BackRed      : 1
% 2.18/1.53  
% 2.18/1.53  #Partial instantiations: 0
% 2.18/1.53  #Strategies tried      : 1
% 2.18/1.53  
% 2.18/1.53  Timing (in seconds)
% 2.18/1.53  ----------------------
% 2.18/1.53  Preprocessing        : 0.41
% 2.18/1.53  Parsing              : 0.22
% 2.18/1.53  CNF conversion       : 0.03
% 2.18/1.53  Main loop            : 0.19
% 2.18/1.53  Inferencing          : 0.08
% 2.18/1.53  Reduction            : 0.05
% 2.18/1.53  Demodulation         : 0.04
% 2.18/1.53  BG Simplification    : 0.01
% 2.18/1.53  Subsumption          : 0.03
% 2.18/1.53  Abstraction          : 0.01
% 2.18/1.53  MUC search           : 0.00
% 2.18/1.53  Cooper               : 0.00
% 2.18/1.54  Total                : 0.65
% 2.18/1.54  Index Insertion      : 0.00
% 2.18/1.54  Index Deletion       : 0.00
% 2.18/1.54  Index Matching       : 0.00
% 2.18/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
