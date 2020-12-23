%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_setfam_1(B_10),A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_setfam_1(B_10),A_9) = k1_setfam_1(B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_32])).

tff(c_72,plain,(
    ! [A_23,B_24,C_25] : k3_xboole_0(k3_xboole_0(A_23,B_24),C_25) = k3_xboole_0(A_23,k3_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [B_31,A_32,C_33] :
      ( k3_xboole_0(k1_setfam_1(B_31),k3_xboole_0(A_32,C_33)) = k3_xboole_0(k1_setfam_1(B_31),C_33)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_233,plain,(
    ! [B_31] :
      ( k3_xboole_0(k1_setfam_1(B_31),k1_xboole_0) = k3_xboole_0(k1_setfam_1(B_31),'#skF_3')
      | ~ r2_hidden('#skF_1',B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_188])).

tff(c_244,plain,(
    ! [B_34] :
      ( k3_xboole_0(k1_setfam_1(B_34),'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_1',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_233])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    k3_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_14])).

tff(c_259,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_30])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.26  
% 2.03/1.27  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 2.03/1.27  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.03/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.27  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.03/1.27  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.27  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.03/1.27  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.27  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_37, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.27  tff(c_45, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.03/1.27  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_setfam_1(B_10), A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.27  tff(c_32, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.27  tff(c_36, plain, (![B_10, A_9]: (k3_xboole_0(k1_setfam_1(B_10), A_9)=k1_setfam_1(B_10) | ~r2_hidden(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_32])).
% 2.03/1.27  tff(c_72, plain, (![A_23, B_24, C_25]: (k3_xboole_0(k3_xboole_0(A_23, B_24), C_25)=k3_xboole_0(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.27  tff(c_188, plain, (![B_31, A_32, C_33]: (k3_xboole_0(k1_setfam_1(B_31), k3_xboole_0(A_32, C_33))=k3_xboole_0(k1_setfam_1(B_31), C_33) | ~r2_hidden(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_36, c_72])).
% 2.03/1.27  tff(c_233, plain, (![B_31]: (k3_xboole_0(k1_setfam_1(B_31), k1_xboole_0)=k3_xboole_0(k1_setfam_1(B_31), '#skF_3') | ~r2_hidden('#skF_1', B_31))), inference(superposition, [status(thm), theory('equality')], [c_45, c_188])).
% 2.03/1.27  tff(c_244, plain, (![B_34]: (k3_xboole_0(k1_setfam_1(B_34), '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_1', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_233])).
% 2.03/1.27  tff(c_26, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.27  tff(c_14, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_30, plain, (k3_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_14])).
% 2.03/1.27  tff(c_259, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_244, c_30])).
% 2.03/1.27  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_259])).
% 2.03/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  Inference rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Ref     : 0
% 2.03/1.27  #Sup     : 61
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 1
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 4
% 2.03/1.27  #Demod        : 42
% 2.03/1.27  #Tautology    : 31
% 2.03/1.27  #SimpNegUnit  : 0
% 2.03/1.27  #BackRed      : 0
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.27  Preprocessing        : 0.28
% 2.03/1.27  Parsing              : 0.16
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.19
% 2.03/1.27  Inferencing          : 0.08
% 2.03/1.28  Reduction            : 0.06
% 2.03/1.28  Demodulation         : 0.05
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.03
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.50
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
