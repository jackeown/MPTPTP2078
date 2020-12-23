%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  30 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [C_7,A_5,B_6] :
      ( k2_wellord1(k2_wellord1(C_7,A_5),B_6) = k2_wellord1(C_7,k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [B_12,A_13] : k1_setfam_1(k2_tarski(B_12,A_13)) = k3_xboole_0(A_13,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [B_12,A_13] : k3_xboole_0(B_12,A_13) = k3_xboole_0(A_13,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_116,plain,(
    ! [C_16,A_17,B_18] :
      ( k2_wellord1(k2_wellord1(C_16,A_17),B_18) = k2_wellord1(C_16,k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_8])).

tff(c_134,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65,c_125])).

tff(c_138,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_134])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  %$ v1_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.20  
% 1.78/1.20  %Foreground sorts:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Background operators:
% 1.78/1.20  
% 1.78/1.20  
% 1.78/1.20  %Foreground operators:
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.78/1.20  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.78/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.78/1.20  
% 1.78/1.20  tff(f_38, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 1.78/1.20  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 1.78/1.20  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.78/1.20  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.78/1.20  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.20  tff(c_6, plain, (![C_7, A_5, B_6]: (k2_wellord1(k2_wellord1(C_7, A_5), B_6)=k2_wellord1(C_7, k3_xboole_0(A_5, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.20  tff(c_44, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.20  tff(c_59, plain, (![B_12, A_13]: (k1_setfam_1(k2_tarski(B_12, A_13))=k3_xboole_0(A_13, B_12))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 1.78/1.20  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.20  tff(c_65, plain, (![B_12, A_13]: (k3_xboole_0(B_12, A_13)=k3_xboole_0(A_13, B_12))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 1.78/1.20  tff(c_116, plain, (![C_16, A_17, B_18]: (k2_wellord1(k2_wellord1(C_16, A_17), B_18)=k2_wellord1(C_16, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.20  tff(c_8, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.20  tff(c_125, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_8])).
% 1.78/1.20  tff(c_134, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65, c_125])).
% 1.78/1.20  tff(c_138, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_134])).
% 1.78/1.20  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 1.78/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  
% 1.78/1.20  Inference rules
% 1.78/1.20  ----------------------
% 1.78/1.20  #Ref     : 0
% 1.78/1.20  #Sup     : 32
% 1.78/1.20  #Fact    : 0
% 1.78/1.20  #Define  : 0
% 1.78/1.20  #Split   : 0
% 1.78/1.20  #Chain   : 0
% 1.78/1.20  #Close   : 0
% 1.78/1.20  
% 1.78/1.20  Ordering : KBO
% 1.78/1.20  
% 1.78/1.20  Simplification rules
% 1.78/1.20  ----------------------
% 1.78/1.20  #Subsume      : 1
% 1.78/1.20  #Demod        : 6
% 1.78/1.20  #Tautology    : 25
% 1.78/1.20  #SimpNegUnit  : 0
% 1.78/1.20  #BackRed      : 0
% 1.78/1.20  
% 1.78/1.20  #Partial instantiations: 0
% 1.78/1.20  #Strategies tried      : 1
% 1.78/1.20  
% 1.78/1.20  Timing (in seconds)
% 1.78/1.20  ----------------------
% 1.78/1.21  Preprocessing        : 0.28
% 1.78/1.21  Parsing              : 0.15
% 1.78/1.21  CNF conversion       : 0.02
% 1.78/1.21  Main loop            : 0.11
% 1.78/1.21  Inferencing          : 0.04
% 1.78/1.21  Reduction            : 0.04
% 1.78/1.21  Demodulation         : 0.03
% 1.78/1.21  BG Simplification    : 0.01
% 1.78/1.21  Subsumption          : 0.02
% 1.78/1.21  Abstraction          : 0.01
% 1.78/1.21  MUC search           : 0.00
% 1.78/1.21  Cooper               : 0.00
% 1.78/1.21  Total                : 0.41
% 1.78/1.21  Index Insertion      : 0.00
% 1.78/1.21  Index Deletion       : 0.00
% 1.78/1.21  Index Matching       : 0.00
% 1.78/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
