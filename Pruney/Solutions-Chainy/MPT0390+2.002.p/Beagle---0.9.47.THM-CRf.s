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
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_setfam_1(B_9),A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [B_23,A_24] :
      ( k3_xboole_0(k1_setfam_1(B_23),A_24) = k1_setfam_1(B_23)
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(k3_xboole_0(A_16,C_17),B_18)
      | ~ r1_tarski(A_16,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_2,A_1,B_18] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_18)
      | ~ r1_tarski(A_1,B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_220,plain,(
    ! [B_30,B_31,A_32] :
      ( r1_tarski(k1_setfam_1(B_30),B_31)
      | ~ r1_tarski(A_32,B_31)
      | ~ r2_hidden(A_32,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_75])).

tff(c_233,plain,(
    ! [B_33] :
      ( r1_tarski(k1_setfam_1(B_33),'#skF_3')
      | ~ r2_hidden('#skF_1',B_33) ) ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_10,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_241,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:16:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.26  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.26  
% 1.92/1.27  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.92/1.27  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.92/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.92/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.92/1.27  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.92/1.27  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.27  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.27  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_setfam_1(B_9), A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.27  tff(c_53, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.27  tff(c_95, plain, (![B_23, A_24]: (k3_xboole_0(k1_setfam_1(B_23), A_24)=k1_setfam_1(B_23) | ~r2_hidden(A_24, B_23))), inference(resolution, [status(thm)], [c_8, c_53])).
% 1.92/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.27  tff(c_66, plain, (![A_16, C_17, B_18]: (r1_tarski(k3_xboole_0(A_16, C_17), B_18) | ~r1_tarski(A_16, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.27  tff(c_75, plain, (![B_2, A_1, B_18]: (r1_tarski(k3_xboole_0(B_2, A_1), B_18) | ~r1_tarski(A_1, B_18))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 1.92/1.27  tff(c_220, plain, (![B_30, B_31, A_32]: (r1_tarski(k1_setfam_1(B_30), B_31) | ~r1_tarski(A_32, B_31) | ~r2_hidden(A_32, B_30))), inference(superposition, [status(thm), theory('equality')], [c_95, c_75])).
% 1.92/1.27  tff(c_233, plain, (![B_33]: (r1_tarski(k1_setfam_1(B_33), '#skF_3') | ~r2_hidden('#skF_1', B_33))), inference(resolution, [status(thm)], [c_12, c_220])).
% 1.92/1.27  tff(c_10, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.27  tff(c_241, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_233, c_10])).
% 1.92/1.27  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_241])).
% 1.92/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  Inference rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Ref     : 0
% 1.92/1.27  #Sup     : 63
% 1.92/1.27  #Fact    : 0
% 1.92/1.27  #Define  : 0
% 1.92/1.27  #Split   : 0
% 1.92/1.27  #Chain   : 0
% 1.92/1.27  #Close   : 0
% 1.92/1.27  
% 1.92/1.27  Ordering : KBO
% 1.92/1.27  
% 1.92/1.27  Simplification rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Subsume      : 11
% 1.92/1.27  #Demod        : 3
% 1.92/1.27  #Tautology    : 20
% 1.92/1.27  #SimpNegUnit  : 0
% 1.92/1.27  #BackRed      : 0
% 1.92/1.27  
% 1.92/1.27  #Partial instantiations: 0
% 1.92/1.27  #Strategies tried      : 1
% 1.92/1.27  
% 1.92/1.27  Timing (in seconds)
% 1.92/1.27  ----------------------
% 1.92/1.28  Preprocessing        : 0.28
% 1.92/1.28  Parsing              : 0.15
% 1.92/1.28  CNF conversion       : 0.02
% 1.92/1.28  Main loop            : 0.19
% 1.92/1.28  Inferencing          : 0.08
% 1.92/1.28  Reduction            : 0.06
% 1.92/1.28  Demodulation         : 0.05
% 1.92/1.28  BG Simplification    : 0.02
% 1.92/1.28  Subsumption          : 0.04
% 1.92/1.28  Abstraction          : 0.01
% 1.92/1.28  MUC search           : 0.00
% 1.92/1.28  Cooper               : 0.00
% 1.92/1.28  Total                : 0.50
% 1.92/1.28  Index Insertion      : 0.00
% 1.92/1.28  Index Deletion       : 0.00
% 1.92/1.28  Index Matching       : 0.00
% 1.92/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
