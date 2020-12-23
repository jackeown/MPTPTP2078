%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,B_19)
      | ~ r1_tarski(A_18,k3_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [B_21,C_22,B_23] : r1_tarski(k3_xboole_0(k3_xboole_0(B_21,C_22),B_23),B_21) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_193,plain,(
    ! [B_27,A_28,B_29] : r1_tarski(k3_xboole_0(k3_xboole_0(B_27,A_28),B_29),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_206,plain,(
    ! [B_29] : r1_tarski(k3_xboole_0('#skF_1',B_29),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_193])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:02:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.86/1.15  
% 1.86/1.15  %Foreground sorts:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Background operators:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Foreground operators:
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.15  
% 1.86/1.16  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.86/1.16  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.86/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.86/1.16  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.86/1.16  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.86/1.16  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.16  tff(c_62, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.16  tff(c_74, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_62])).
% 1.86/1.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.16  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.16  tff(c_102, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, B_19) | ~r1_tarski(A_18, k3_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.16  tff(c_126, plain, (![B_21, C_22, B_23]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_21, C_22), B_23), B_21))), inference(resolution, [status(thm)], [c_4, c_102])).
% 1.86/1.16  tff(c_193, plain, (![B_27, A_28, B_29]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_27, A_28), B_29), A_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 1.86/1.16  tff(c_206, plain, (![B_29]: (r1_tarski(k3_xboole_0('#skF_1', B_29), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_193])).
% 1.86/1.16  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.16  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_10])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 63
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 0
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 2
% 1.86/1.16  #Demod        : 18
% 1.86/1.16  #Tautology    : 32
% 1.86/1.16  #SimpNegUnit  : 0
% 1.86/1.16  #BackRed      : 1
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.24
% 1.86/1.16  Parsing              : 0.13
% 1.86/1.16  CNF conversion       : 0.01
% 1.86/1.16  Main loop            : 0.18
% 1.86/1.16  Inferencing          : 0.06
% 1.86/1.16  Reduction            : 0.07
% 1.86/1.16  Demodulation         : 0.06
% 1.86/1.16  BG Simplification    : 0.01
% 1.86/1.16  Subsumption          : 0.03
% 1.86/1.16  Abstraction          : 0.01
% 1.86/1.16  MUC search           : 0.00
% 1.86/1.16  Cooper               : 0.00
% 1.86/1.16  Total                : 0.43
% 1.86/1.16  Index Insertion      : 0.00
% 1.86/1.16  Index Deletion       : 0.00
% 1.86/1.16  Index Matching       : 0.00
% 1.86/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
