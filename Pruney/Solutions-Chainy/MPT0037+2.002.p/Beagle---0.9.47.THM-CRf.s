%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:41 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  35 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  30 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_89,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k3_xboole_0(A_16,B_17),k3_xboole_0(A_16,C_18)) = k3_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    ! [B_21,B_22,A_23] : k2_xboole_0(k3_xboole_0(B_21,B_22),k3_xboole_0(A_23,B_21)) = k3_xboole_0(B_21,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_227,plain,(
    ! [B_22] : k3_xboole_0('#skF_2',k2_xboole_0(B_22,'#skF_1')) = k2_xboole_0(k3_xboole_0('#skF_2',B_22),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_189])).

tff(c_298,plain,(
    ! [B_25] : k3_xboole_0('#skF_2',k2_xboole_0(B_25,'#skF_1')) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_320,plain,(
    ! [A_1] : k3_xboole_0('#skF_2',k2_xboole_0('#skF_1',A_1)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_298])).

tff(c_10,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_765,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_13])).

tff(c_768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.55/1.37  
% 2.55/1.37  %Foreground sorts:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Background operators:
% 2.55/1.37  
% 2.55/1.37  
% 2.55/1.37  %Foreground operators:
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.37  
% 2.66/1.37  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.66/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.66/1.37  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => (k2_xboole_0(A, k3_xboole_0(C, B)) = k3_xboole_0(k2_xboole_0(A, C), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_xboole_1)).
% 2.66/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.37  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.66/1.37  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.37  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.37  tff(c_80, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.37  tff(c_84, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_80])).
% 2.66/1.37  tff(c_89, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k3_xboole_0(A_16, C_18))=k3_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.37  tff(c_189, plain, (![B_21, B_22, A_23]: (k2_xboole_0(k3_xboole_0(B_21, B_22), k3_xboole_0(A_23, B_21))=k3_xboole_0(B_21, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_89])).
% 2.66/1.37  tff(c_227, plain, (![B_22]: (k3_xboole_0('#skF_2', k2_xboole_0(B_22, '#skF_1'))=k2_xboole_0(k3_xboole_0('#skF_2', B_22), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_189])).
% 2.66/1.37  tff(c_298, plain, (![B_25]: (k3_xboole_0('#skF_2', k2_xboole_0(B_25, '#skF_1'))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_227])).
% 2.66/1.37  tff(c_320, plain, (![A_1]: (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', A_1))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_298])).
% 2.66/1.37  tff(c_10, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.37  tff(c_13, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 2.66/1.37  tff(c_765, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_13])).
% 2.66/1.37  tff(c_768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_765])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 201
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 0
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 4
% 2.66/1.38  #Demod        : 44
% 2.66/1.38  #Tautology    : 94
% 2.66/1.38  #SimpNegUnit  : 0
% 2.66/1.38  #BackRed      : 1
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.27
% 2.66/1.38  Parsing              : 0.15
% 2.66/1.38  CNF conversion       : 0.01
% 2.66/1.38  Main loop            : 0.36
% 2.66/1.38  Inferencing          : 0.12
% 2.66/1.38  Reduction            : 0.15
% 2.66/1.38  Demodulation         : 0.13
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.05
% 2.66/1.38  Abstraction          : 0.02
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.65
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
