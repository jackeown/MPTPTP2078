%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:52 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  48 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [C_7,A_5,B_6] :
      ( k7_relat_1(k7_relat_1(C_7,A_5),B_6) = k7_relat_1(C_7,k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [C_22,A_23,B_24] :
      ( k7_relat_1(k7_relat_1(C_22,A_23),B_24) = k7_relat_1(C_22,A_23)
      | ~ r1_tarski(A_23,B_24)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [C_25,A_26,B_27] :
      ( k7_relat_1(C_25,k3_xboole_0(A_26,B_27)) = k7_relat_1(C_25,A_26)
      | ~ r1_tarski(A_26,B_27)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_15,A_16] : k1_setfam_1(k2_tarski(B_15,A_16)) = k3_xboole_0(A_16,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [B_15,A_16] : k3_xboole_0(B_15,A_16) = k3_xboole_0(A_16,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_120,plain,(
    ! [C_19,A_20,B_21] :
      ( k7_relat_1(k7_relat_1(C_19,A_20),B_21) = k7_relat_1(C_19,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_138,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_69,c_129])).

tff(c_186,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_138])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:34:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.19  
% 1.84/1.19  %Foreground sorts:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Background operators:
% 1.84/1.19  
% 1.84/1.19  
% 1.84/1.19  %Foreground operators:
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.84/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.84/1.19  
% 1.84/1.20  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 1.84/1.20  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.84/1.20  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.84/1.20  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.84/1.20  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.84/1.20  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.20  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.20  tff(c_6, plain, (![C_7, A_5, B_6]: (k7_relat_1(k7_relat_1(C_7, A_5), B_6)=k7_relat_1(C_7, k3_xboole_0(A_5, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.20  tff(c_140, plain, (![C_22, A_23, B_24]: (k7_relat_1(k7_relat_1(C_22, A_23), B_24)=k7_relat_1(C_22, A_23) | ~r1_tarski(A_23, B_24) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.20  tff(c_173, plain, (![C_25, A_26, B_27]: (k7_relat_1(C_25, k3_xboole_0(A_26, B_27))=k7_relat_1(C_25, A_26) | ~r1_tarski(A_26, B_27) | ~v1_relat_1(C_25) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_140])).
% 1.84/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.20  tff(c_48, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.20  tff(c_63, plain, (![B_15, A_16]: (k1_setfam_1(k2_tarski(B_15, A_16))=k3_xboole_0(A_16, B_15))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 1.84/1.20  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.20  tff(c_69, plain, (![B_15, A_16]: (k3_xboole_0(B_15, A_16)=k3_xboole_0(A_16, B_15))), inference(superposition, [status(thm), theory('equality')], [c_63, c_4])).
% 1.84/1.20  tff(c_120, plain, (![C_19, A_20, B_21]: (k7_relat_1(k7_relat_1(C_19, A_20), B_21)=k7_relat_1(C_19, k3_xboole_0(A_20, B_21)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.20  tff(c_10, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.20  tff(c_129, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 1.84/1.20  tff(c_138, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_69, c_129])).
% 1.84/1.20  tff(c_186, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_173, c_138])).
% 1.84/1.20  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_186])).
% 1.84/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.20  
% 1.84/1.20  Inference rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Ref     : 0
% 1.84/1.20  #Sup     : 51
% 1.84/1.20  #Fact    : 0
% 1.84/1.20  #Define  : 0
% 1.84/1.20  #Split   : 1
% 1.84/1.20  #Chain   : 0
% 1.84/1.20  #Close   : 0
% 1.84/1.20  
% 1.84/1.20  Ordering : KBO
% 1.84/1.20  
% 1.84/1.20  Simplification rules
% 1.84/1.20  ----------------------
% 1.84/1.20  #Subsume      : 1
% 1.84/1.20  #Demod        : 8
% 1.84/1.20  #Tautology    : 28
% 1.84/1.20  #SimpNegUnit  : 0
% 1.84/1.20  #BackRed      : 0
% 1.84/1.20  
% 1.84/1.20  #Partial instantiations: 0
% 1.84/1.20  #Strategies tried      : 1
% 1.84/1.20  
% 1.84/1.20  Timing (in seconds)
% 1.84/1.20  ----------------------
% 1.84/1.20  Preprocessing        : 0.26
% 1.84/1.20  Parsing              : 0.14
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.17
% 1.84/1.20  Inferencing          : 0.06
% 1.84/1.20  Reduction            : 0.06
% 1.84/1.20  Demodulation         : 0.05
% 1.84/1.20  BG Simplification    : 0.01
% 1.84/1.20  Subsumption          : 0.02
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.45
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
