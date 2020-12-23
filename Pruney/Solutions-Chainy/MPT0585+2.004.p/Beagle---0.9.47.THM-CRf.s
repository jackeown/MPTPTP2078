%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  62 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_10] :
      ( k7_relat_1(A_10,k1_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_185,plain,(
    ! [C_25,A_26,B_27] :
      ( k7_relat_1(k7_relat_1(C_25,A_26),B_27) = k7_relat_1(C_25,k3_xboole_0(A_26,B_27))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_211,plain,(
    ! [A_28,B_29] :
      ( k7_relat_1(A_28,k3_xboole_0(k1_relat_1(A_28),B_29)) = k7_relat_1(A_28,B_29)
      | ~ v1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_396,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,k1_relat_1(k7_relat_1(B_34,A_35))) = k7_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_211])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [B_19,A_20] : k1_setfam_1(k2_tarski(B_19,A_20)) = k3_xboole_0(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_106,plain,(
    ! [B_21,A_22] : k3_xboole_0(B_21,A_22) = k3_xboole_0(A_22,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_4])).

tff(c_154,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,k1_relat_1(B_24)) = k1_relat_1(k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_291,plain,(
    ! [B_33,B_32] :
      ( k1_relat_1(k7_relat_1(B_33,k1_relat_1(B_32))) = k1_relat_1(k7_relat_1(B_32,k1_relat_1(B_33)))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_8])).

tff(c_12,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_336,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_12])).

tff(c_389,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_336])).

tff(c_405,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_389])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:44:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  %$ v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.35  
% 2.21/1.36  tff(f_49, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.21/1.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.21/1.36  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.21/1.36  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.21/1.36  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.21/1.36  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.21/1.36  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.36  tff(c_8, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.36  tff(c_10, plain, (![A_10]: (k7_relat_1(A_10, k1_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.36  tff(c_185, plain, (![C_25, A_26, B_27]: (k7_relat_1(k7_relat_1(C_25, A_26), B_27)=k7_relat_1(C_25, k3_xboole_0(A_26, B_27)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.36  tff(c_211, plain, (![A_28, B_29]: (k7_relat_1(A_28, k3_xboole_0(k1_relat_1(A_28), B_29))=k7_relat_1(A_28, B_29) | ~v1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_10, c_185])).
% 2.21/1.36  tff(c_396, plain, (![B_34, A_35]: (k7_relat_1(B_34, k1_relat_1(k7_relat_1(B_34, A_35)))=k7_relat_1(B_34, A_35) | ~v1_relat_1(B_34) | ~v1_relat_1(B_34) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_211])).
% 2.21/1.36  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.36  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.36  tff(c_59, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.36  tff(c_83, plain, (![B_19, A_20]: (k1_setfam_1(k2_tarski(B_19, A_20))=k3_xboole_0(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_59])).
% 2.21/1.36  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.36  tff(c_106, plain, (![B_21, A_22]: (k3_xboole_0(B_21, A_22)=k3_xboole_0(A_22, B_21))), inference(superposition, [status(thm), theory('equality')], [c_83, c_4])).
% 2.21/1.36  tff(c_154, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k1_relat_1(B_24))=k1_relat_1(k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 2.21/1.36  tff(c_291, plain, (![B_33, B_32]: (k1_relat_1(k7_relat_1(B_33, k1_relat_1(B_32)))=k1_relat_1(k7_relat_1(B_32, k1_relat_1(B_33))) | ~v1_relat_1(B_32) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_154, c_8])).
% 2.21/1.36  tff(c_12, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.36  tff(c_336, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_12])).
% 2.21/1.36  tff(c_389, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_336])).
% 2.21/1.36  tff(c_405, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_396, c_389])).
% 2.21/1.36  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_405])).
% 2.21/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.36  
% 2.21/1.36  Inference rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Ref     : 0
% 2.21/1.36  #Sup     : 113
% 2.21/1.36  #Fact    : 0
% 2.21/1.36  #Define  : 0
% 2.21/1.36  #Split   : 0
% 2.21/1.36  #Chain   : 0
% 2.21/1.36  #Close   : 0
% 2.21/1.36  
% 2.21/1.36  Ordering : KBO
% 2.21/1.36  
% 2.21/1.36  Simplification rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Subsume      : 13
% 2.21/1.36  #Demod        : 8
% 2.21/1.36  #Tautology    : 47
% 2.21/1.36  #SimpNegUnit  : 0
% 2.21/1.36  #BackRed      : 0
% 2.21/1.36  
% 2.21/1.36  #Partial instantiations: 0
% 2.21/1.36  #Strategies tried      : 1
% 2.21/1.36  
% 2.21/1.36  Timing (in seconds)
% 2.21/1.36  ----------------------
% 2.21/1.36  Preprocessing        : 0.29
% 2.21/1.36  Parsing              : 0.16
% 2.21/1.36  CNF conversion       : 0.02
% 2.21/1.36  Main loop            : 0.25
% 2.21/1.36  Inferencing          : 0.11
% 2.21/1.36  Reduction            : 0.07
% 2.21/1.36  Demodulation         : 0.06
% 2.21/1.36  BG Simplification    : 0.02
% 2.21/1.36  Subsumption          : 0.04
% 2.21/1.36  Abstraction          : 0.02
% 2.21/1.36  MUC search           : 0.00
% 2.21/1.36  Cooper               : 0.00
% 2.21/1.36  Total                : 0.57
% 2.21/1.36  Index Insertion      : 0.00
% 2.21/1.36  Index Deletion       : 0.00
% 2.21/1.36  Index Matching       : 0.00
% 2.21/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
