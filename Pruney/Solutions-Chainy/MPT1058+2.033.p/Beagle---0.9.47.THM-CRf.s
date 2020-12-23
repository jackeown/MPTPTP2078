%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  36 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_18,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_99,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_99])).

tff(c_120,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_114])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( k3_xboole_0(A_12,k10_relat_1(C_14,B_13)) = k10_relat_1(k7_relat_1(C_14,A_12),B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_194,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_16])).

tff(c_201,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_194])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.26  
% 2.01/1.26  tff(f_53, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.01/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.01/1.26  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.01/1.26  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.01/1.26  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.01/1.26  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.01/1.26  tff(c_18, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.26  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.26  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.26  tff(c_20, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.26  tff(c_77, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.26  tff(c_85, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.01/1.26  tff(c_99, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.26  tff(c_114, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_99])).
% 2.01/1.26  tff(c_120, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_114])).
% 2.01/1.26  tff(c_16, plain, (![A_12, C_14, B_13]: (k3_xboole_0(A_12, k10_relat_1(C_14, B_13))=k10_relat_1(k7_relat_1(C_14, A_12), B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.26  tff(c_194, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_120, c_16])).
% 2.01/1.26  tff(c_201, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_194])).
% 2.01/1.26  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_201])).
% 2.01/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  Inference rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Ref     : 0
% 2.01/1.26  #Sup     : 47
% 2.01/1.26  #Fact    : 0
% 2.01/1.26  #Define  : 0
% 2.01/1.26  #Split   : 0
% 2.01/1.26  #Chain   : 0
% 2.01/1.26  #Close   : 0
% 2.01/1.26  
% 2.01/1.26  Ordering : KBO
% 2.01/1.26  
% 2.01/1.26  Simplification rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Subsume      : 2
% 2.01/1.26  #Demod        : 6
% 2.01/1.26  #Tautology    : 28
% 2.01/1.26  #SimpNegUnit  : 1
% 2.01/1.26  #BackRed      : 0
% 2.01/1.26  
% 2.01/1.26  #Partial instantiations: 0
% 2.01/1.26  #Strategies tried      : 1
% 2.01/1.26  
% 2.01/1.26  Timing (in seconds)
% 2.01/1.26  ----------------------
% 2.01/1.27  Preprocessing        : 0.31
% 2.01/1.27  Parsing              : 0.16
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.15
% 2.01/1.27  Inferencing          : 0.06
% 2.01/1.27  Reduction            : 0.05
% 2.01/1.27  Demodulation         : 0.04
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.02
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.48
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
