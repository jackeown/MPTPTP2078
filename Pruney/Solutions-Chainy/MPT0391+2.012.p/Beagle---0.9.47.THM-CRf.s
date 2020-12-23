%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_setfam_1(B_10),A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_55,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_55])).

tff(c_67,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_75,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_xboole_0(A_23,C_24)
      | ~ r1_tarski(A_23,k4_xboole_0(B_25,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_26] :
      ( r1_xboole_0(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_75])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:32:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  
% 1.56/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.56/1.14  
% 1.56/1.14  %Foreground sorts:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Background operators:
% 1.56/1.14  
% 1.56/1.14  
% 1.56/1.14  %Foreground operators:
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.56/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.56/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.56/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.56/1.14  
% 1.56/1.15  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.56/1.15  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.56/1.15  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.56/1.15  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.56/1.15  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.56/1.15  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.56/1.15  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.56/1.15  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k1_setfam_1(B_10), A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.56/1.15  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.15  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.56/1.15  tff(c_35, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.15  tff(c_43, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_35])).
% 1.56/1.15  tff(c_55, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.15  tff(c_64, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43, c_55])).
% 1.56/1.15  tff(c_67, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_64])).
% 1.56/1.15  tff(c_75, plain, (![A_23, C_24, B_25]: (r1_xboole_0(A_23, C_24) | ~r1_tarski(A_23, k4_xboole_0(B_25, C_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.56/1.15  tff(c_84, plain, (![A_26]: (r1_xboole_0(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_75])).
% 1.56/1.15  tff(c_16, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.56/1.15  tff(c_92, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_84, c_16])).
% 1.56/1.15  tff(c_95, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_92])).
% 1.56/1.15  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 1.56/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.15  
% 1.56/1.15  Inference rules
% 1.56/1.15  ----------------------
% 1.56/1.15  #Ref     : 0
% 1.56/1.15  #Sup     : 19
% 1.56/1.15  #Fact    : 0
% 1.56/1.15  #Define  : 0
% 1.56/1.15  #Split   : 0
% 1.56/1.15  #Chain   : 0
% 1.56/1.15  #Close   : 0
% 1.56/1.15  
% 1.56/1.15  Ordering : KBO
% 1.56/1.15  
% 1.56/1.15  Simplification rules
% 1.56/1.15  ----------------------
% 1.56/1.15  #Subsume      : 0
% 1.56/1.15  #Demod        : 2
% 1.56/1.15  #Tautology    : 10
% 1.56/1.15  #SimpNegUnit  : 0
% 1.56/1.15  #BackRed      : 0
% 1.56/1.15  
% 1.56/1.15  #Partial instantiations: 0
% 1.56/1.15  #Strategies tried      : 1
% 1.56/1.15  
% 1.56/1.15  Timing (in seconds)
% 1.56/1.15  ----------------------
% 1.56/1.15  Preprocessing        : 0.27
% 1.56/1.15  Parsing              : 0.15
% 1.56/1.15  CNF conversion       : 0.02
% 1.56/1.15  Main loop            : 0.12
% 1.56/1.15  Inferencing          : 0.05
% 1.56/1.15  Reduction            : 0.03
% 1.56/1.15  Demodulation         : 0.02
% 1.56/1.15  BG Simplification    : 0.01
% 1.56/1.15  Subsumption          : 0.02
% 1.56/1.16  Abstraction          : 0.00
% 1.56/1.16  MUC search           : 0.00
% 1.56/1.16  Cooper               : 0.00
% 1.56/1.16  Total                : 0.41
% 1.56/1.16  Index Insertion      : 0.00
% 1.56/1.16  Index Deletion       : 0.00
% 1.56/1.16  Index Matching       : 0.00
% 1.56/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
