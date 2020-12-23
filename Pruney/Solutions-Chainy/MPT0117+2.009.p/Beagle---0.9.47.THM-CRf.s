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
% DateTime   : Thu Dec  3 09:45:30 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   33 (  45 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  54 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,k3_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [B_26,C_27,B_28] : r1_tarski(k4_xboole_0(k3_xboole_0(B_26,C_27),B_28),B_26) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_145,plain,(
    ! [B_29,A_30,B_31] : r1_tarski(k4_xboole_0(k3_xboole_0(B_29,A_30),B_31),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_158,plain,(
    ! [B_31] : r1_tarski(k4_xboole_0('#skF_3',B_31),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_145])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_53])).

tff(c_155,plain,(
    ! [B_31] : r1_tarski(k4_xboole_0('#skF_1',B_31),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_145])).

tff(c_174,plain,(
    ! [A_33,B_34,C_35] :
      ( r1_tarski(k5_xboole_0(A_33,B_34),C_35)
      | ~ r1_tarski(k4_xboole_0(B_34,A_33),C_35)
      | ~ r1_tarski(k4_xboole_0(A_33,B_34),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_184,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_14])).

tff(c_198,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_184])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.26  
% 1.89/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.26  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.89/1.26  
% 1.89/1.26  %Foreground sorts:
% 1.89/1.26  
% 1.89/1.26  
% 1.89/1.26  %Background operators:
% 1.89/1.26  
% 1.89/1.26  
% 1.89/1.26  %Foreground operators:
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.89/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.26  
% 1.89/1.27  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 1.89/1.27  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.89/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.89/1.27  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.89/1.27  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.89/1.27  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 1.89/1.27  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.27  tff(c_53, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.27  tff(c_64, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.89/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.27  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.27  tff(c_103, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_tarski(A_23, k3_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.27  tff(c_121, plain, (![B_26, C_27, B_28]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_26, C_27), B_28), B_26))), inference(resolution, [status(thm)], [c_10, c_103])).
% 1.89/1.27  tff(c_145, plain, (![B_29, A_30, B_31]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_29, A_30), B_31), A_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 1.89/1.27  tff(c_158, plain, (![B_31]: (r1_tarski(k4_xboole_0('#skF_3', B_31), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_145])).
% 1.89/1.27  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.27  tff(c_65, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_53])).
% 1.89/1.27  tff(c_155, plain, (![B_31]: (r1_tarski(k4_xboole_0('#skF_1', B_31), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_145])).
% 1.89/1.27  tff(c_174, plain, (![A_33, B_34, C_35]: (r1_tarski(k5_xboole_0(A_33, B_34), C_35) | ~r1_tarski(k4_xboole_0(B_34, A_33), C_35) | ~r1_tarski(k4_xboole_0(A_33, B_34), C_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.27  tff(c_14, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.27  tff(c_184, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_174, c_14])).
% 1.89/1.27  tff(c_198, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_184])).
% 1.89/1.27  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_198])).
% 1.89/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.27  
% 1.89/1.27  Inference rules
% 1.89/1.27  ----------------------
% 1.89/1.27  #Ref     : 0
% 1.89/1.27  #Sup     : 50
% 1.89/1.27  #Fact    : 0
% 1.89/1.27  #Define  : 0
% 1.89/1.27  #Split   : 0
% 1.89/1.27  #Chain   : 0
% 1.89/1.27  #Close   : 0
% 1.89/1.27  
% 1.89/1.27  Ordering : KBO
% 1.89/1.27  
% 1.89/1.27  Simplification rules
% 1.89/1.27  ----------------------
% 1.89/1.27  #Subsume      : 0
% 1.89/1.27  #Demod        : 6
% 1.89/1.27  #Tautology    : 24
% 1.89/1.27  #SimpNegUnit  : 0
% 1.89/1.27  #BackRed      : 0
% 1.89/1.27  
% 1.89/1.27  #Partial instantiations: 0
% 1.89/1.27  #Strategies tried      : 1
% 1.89/1.27  
% 1.89/1.27  Timing (in seconds)
% 1.89/1.27  ----------------------
% 1.89/1.27  Preprocessing        : 0.28
% 1.89/1.27  Parsing              : 0.16
% 1.89/1.27  CNF conversion       : 0.02
% 1.89/1.28  Main loop            : 0.16
% 1.89/1.28  Inferencing          : 0.06
% 1.89/1.28  Reduction            : 0.06
% 1.89/1.28  Demodulation         : 0.05
% 1.89/1.28  BG Simplification    : 0.01
% 1.89/1.28  Subsumption          : 0.03
% 1.89/1.28  Abstraction          : 0.01
% 1.89/1.28  MUC search           : 0.00
% 1.89/1.28  Cooper               : 0.00
% 1.89/1.28  Total                : 0.47
% 1.89/1.28  Index Insertion      : 0.00
% 1.89/1.28  Index Deletion       : 0.00
% 1.89/1.28  Index Matching       : 0.00
% 1.89/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
