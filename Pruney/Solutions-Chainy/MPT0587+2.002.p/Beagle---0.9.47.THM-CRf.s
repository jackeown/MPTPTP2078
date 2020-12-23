%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:02 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  35 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_226,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k1_relat_1(B_37),A_38) = k1_relat_1(k7_relat_1(B_37,A_38))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_31,B_32] : k3_xboole_0(k4_xboole_0(A_31,B_32),A_31) = k4_xboole_0(A_31,B_32) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [B_25,A_26] : k1_setfam_1(k2_tarski(B_25,A_26)) = k3_xboole_0(A_26,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_12,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_164,plain,(
    ! [A_31,B_32] : k3_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_89])).

tff(c_360,plain,(
    ! [B_49,B_50] :
      ( k1_relat_1(k7_relat_1(B_49,k4_xboole_0(k1_relat_1(B_49),B_50))) = k4_xboole_0(k1_relat_1(B_49),B_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_164])).

tff(c_10,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k6_subset_1(k1_relat_1('#skF_2'),'#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_384,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_19])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.26  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.26  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.26  
% 2.03/1.27  tff(f_48, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 2.03/1.27  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.03/1.27  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.03/1.27  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.03/1.27  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.03/1.27  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.03/1.27  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.03/1.27  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_226, plain, (![B_37, A_38]: (k3_xboole_0(k1_relat_1(B_37), A_38)=k1_relat_1(k7_relat_1(B_37, A_38)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.27  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.27  tff(c_63, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.27  tff(c_155, plain, (![A_31, B_32]: (k3_xboole_0(k4_xboole_0(A_31, B_32), A_31)=k4_xboole_0(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.03/1.27  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.27  tff(c_68, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.27  tff(c_83, plain, (![B_25, A_26]: (k1_setfam_1(k2_tarski(B_25, A_26))=k3_xboole_0(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.03/1.27  tff(c_12, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.27  tff(c_89, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 2.03/1.27  tff(c_164, plain, (![A_31, B_32]: (k3_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_155, c_89])).
% 2.03/1.27  tff(c_360, plain, (![B_49, B_50]: (k1_relat_1(k7_relat_1(B_49, k4_xboole_0(k1_relat_1(B_49), B_50)))=k4_xboole_0(k1_relat_1(B_49), B_50) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_226, c_164])).
% 2.03/1.27  tff(c_10, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.27  tff(c_16, plain, (k1_relat_1(k7_relat_1('#skF_2', k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.27  tff(c_19, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.03/1.27  tff(c_384, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_360, c_19])).
% 2.03/1.27  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_384])).
% 2.03/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  Inference rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Ref     : 0
% 2.03/1.27  #Sup     : 93
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 0
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 9
% 2.03/1.27  #Demod        : 16
% 2.03/1.27  #Tautology    : 60
% 2.03/1.27  #SimpNegUnit  : 0
% 2.03/1.27  #BackRed      : 0
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.27  Preprocessing        : 0.29
% 2.03/1.27  Parsing              : 0.15
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.22
% 2.03/1.27  Inferencing          : 0.09
% 2.03/1.27  Reduction            : 0.07
% 2.03/1.27  Demodulation         : 0.06
% 2.03/1.27  BG Simplification    : 0.02
% 2.03/1.27  Subsumption          : 0.03
% 2.03/1.27  Abstraction          : 0.02
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.54
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.27  Index Matching       : 0.00
% 2.03/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
