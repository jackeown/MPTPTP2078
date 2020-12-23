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
% DateTime   : Thu Dec  3 10:06:39 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_41,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_29] : k1_setfam_1(k1_tarski(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = k1_setfam_1(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_55,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_92,plain,(
    ! [C_49,A_50,B_51] :
      ( k2_wellord1(k2_wellord1(C_49,A_50),B_51) = k2_wellord1(C_49,k3_xboole_0(A_50,B_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    k2_wellord1(k2_wellord1('#skF_2','#skF_1'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101,plain,
    ( k2_wellord1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_22])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_55,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.46  
% 2.21/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.47  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > #skF_2 > #skF_1
% 2.21/1.47  
% 2.21/1.47  %Foreground sorts:
% 2.21/1.47  
% 2.21/1.47  
% 2.21/1.47  %Background operators:
% 2.21/1.47  
% 2.21/1.47  
% 2.21/1.47  %Foreground operators:
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.47  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.21/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.47  
% 2.21/1.48  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 2.21/1.48  tff(f_41, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.21/1.48  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.48  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.21/1.48  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 2.21/1.48  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.48  tff(c_16, plain, (![A_29]: (k1_setfam_1(k1_tarski(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.48  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.48  tff(c_43, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.48  tff(c_52, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=k1_setfam_1(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 2.21/1.48  tff(c_55, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 2.21/1.48  tff(c_92, plain, (![C_49, A_50, B_51]: (k2_wellord1(k2_wellord1(C_49, A_50), B_51)=k2_wellord1(C_49, k3_xboole_0(A_50, B_51)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.48  tff(c_22, plain, (k2_wellord1(k2_wellord1('#skF_2', '#skF_1'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.48  tff(c_101, plain, (k2_wellord1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_22])).
% 2.21/1.48  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_55, c_101])).
% 2.21/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.48  
% 2.21/1.48  Inference rules
% 2.21/1.48  ----------------------
% 2.21/1.48  #Ref     : 0
% 2.21/1.48  #Sup     : 20
% 2.21/1.48  #Fact    : 0
% 2.21/1.48  #Define  : 0
% 2.21/1.48  #Split   : 0
% 2.21/1.48  #Chain   : 0
% 2.21/1.48  #Close   : 0
% 2.21/1.48  
% 2.21/1.48  Ordering : KBO
% 2.21/1.48  
% 2.21/1.48  Simplification rules
% 2.21/1.48  ----------------------
% 2.21/1.48  #Subsume      : 0
% 2.21/1.48  #Demod        : 3
% 2.21/1.48  #Tautology    : 15
% 2.21/1.48  #SimpNegUnit  : 0
% 2.21/1.48  #BackRed      : 0
% 2.21/1.48  
% 2.21/1.48  #Partial instantiations: 0
% 2.21/1.48  #Strategies tried      : 1
% 2.21/1.48  
% 2.21/1.48  Timing (in seconds)
% 2.21/1.48  ----------------------
% 2.21/1.49  Preprocessing        : 0.47
% 2.21/1.49  Parsing              : 0.24
% 2.21/1.49  CNF conversion       : 0.03
% 2.21/1.49  Main loop            : 0.16
% 2.21/1.49  Inferencing          : 0.07
% 2.21/1.49  Reduction            : 0.05
% 2.21/1.49  Demodulation         : 0.04
% 2.21/1.49  BG Simplification    : 0.02
% 2.21/1.49  Subsumption          : 0.02
% 2.21/1.49  Abstraction          : 0.02
% 2.21/1.49  MUC search           : 0.00
% 2.21/1.49  Cooper               : 0.00
% 2.21/1.49  Total                : 0.67
% 2.21/1.49  Index Insertion      : 0.00
% 2.21/1.49  Index Deletion       : 0.00
% 2.21/1.49  Index Matching       : 0.00
% 2.21/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
