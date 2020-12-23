%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
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
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

tff(f_41,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

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
      ( k7_relat_1(k7_relat_1(C_49,A_50),B_51) = k7_relat_1(C_49,k3_xboole_0(A_50,B_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101,plain,
    ( k7_relat_1('#skF_2',k3_xboole_0('#skF_1','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_22])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_55,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.16  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > #skF_2 > #skF_1
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.77/1.16  
% 1.77/1.17  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 1.77/1.17  tff(f_41, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.77/1.17  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.77/1.17  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.77/1.17  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.77/1.17  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.17  tff(c_16, plain, (![A_29]: (k1_setfam_1(k1_tarski(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.17  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.17  tff(c_43, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.77/1.17  tff(c_52, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=k1_setfam_1(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 1.77/1.17  tff(c_55, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 1.77/1.17  tff(c_92, plain, (![C_49, A_50, B_51]: (k7_relat_1(k7_relat_1(C_49, A_50), B_51)=k7_relat_1(C_49, k3_xboole_0(A_50, B_51)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.17  tff(c_22, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.17  tff(c_101, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_22])).
% 1.77/1.17  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_55, c_101])).
% 1.77/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  Inference rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Ref     : 0
% 1.77/1.17  #Sup     : 20
% 1.77/1.17  #Fact    : 0
% 1.77/1.17  #Define  : 0
% 1.77/1.17  #Split   : 0
% 1.77/1.17  #Chain   : 0
% 1.77/1.17  #Close   : 0
% 1.77/1.17  
% 1.77/1.17  Ordering : KBO
% 1.77/1.17  
% 1.77/1.17  Simplification rules
% 1.77/1.17  ----------------------
% 1.77/1.17  #Subsume      : 0
% 1.77/1.17  #Demod        : 3
% 1.77/1.17  #Tautology    : 15
% 1.77/1.17  #SimpNegUnit  : 0
% 1.77/1.17  #BackRed      : 0
% 1.77/1.17  
% 1.77/1.17  #Partial instantiations: 0
% 1.77/1.17  #Strategies tried      : 1
% 1.77/1.17  
% 1.77/1.17  Timing (in seconds)
% 1.77/1.17  ----------------------
% 1.77/1.17  Preprocessing        : 0.28
% 1.77/1.17  Parsing              : 0.15
% 1.77/1.17  CNF conversion       : 0.02
% 1.77/1.17  Main loop            : 0.12
% 1.77/1.17  Inferencing          : 0.06
% 1.77/1.17  Reduction            : 0.03
% 1.77/1.17  Demodulation         : 0.03
% 1.77/1.17  BG Simplification    : 0.01
% 1.77/1.17  Subsumption          : 0.01
% 1.77/1.17  Abstraction          : 0.01
% 1.77/1.17  MUC search           : 0.00
% 1.77/1.17  Cooper               : 0.00
% 1.77/1.17  Total                : 0.43
% 1.77/1.17  Index Insertion      : 0.00
% 1.77/1.17  Index Deletion       : 0.00
% 1.77/1.17  Index Matching       : 0.00
% 1.77/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
