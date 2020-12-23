%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_20,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_325,plain,(
    ! [A_45,C_46,B_47] :
      ( k3_xboole_0(A_45,k10_relat_1(C_46,B_47)) = k10_relat_1(k7_relat_1(C_46,A_45),B_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_16])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_164,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_164])).

tff(c_185,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6,c_179])).

tff(c_338,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_185])).

tff(c_361,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_338])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.67  
% 2.48/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.67  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.67  
% 2.48/1.67  %Foreground sorts:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Background operators:
% 2.48/1.67  
% 2.48/1.67  
% 2.48/1.67  %Foreground operators:
% 2.48/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.67  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.48/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.67  
% 2.48/1.69  tff(f_55, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.48/1.69  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.48/1.69  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.48/1.69  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.48/1.69  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.48/1.69  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.48/1.69  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.48/1.69  tff(c_20, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.69  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.69  tff(c_325, plain, (![A_45, C_46, B_47]: (k3_xboole_0(A_45, k10_relat_1(C_46, B_47))=k10_relat_1(k7_relat_1(C_46, A_45), B_47) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.69  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.69  tff(c_78, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.69  tff(c_107, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_78])).
% 2.48/1.69  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.69  tff(c_113, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_107, c_16])).
% 2.48/1.69  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.69  tff(c_22, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.69  tff(c_69, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.69  tff(c_73, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_69])).
% 2.48/1.69  tff(c_164, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.69  tff(c_179, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_164])).
% 2.48/1.69  tff(c_185, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_6, c_179])).
% 2.48/1.69  tff(c_338, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_325, c_185])).
% 2.48/1.69  tff(c_361, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_338])).
% 2.48/1.69  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_361])).
% 2.48/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.69  
% 2.48/1.69  Inference rules
% 2.48/1.69  ----------------------
% 2.48/1.69  #Ref     : 0
% 2.48/1.69  #Sup     : 86
% 2.48/1.69  #Fact    : 0
% 2.48/1.69  #Define  : 0
% 2.48/1.69  #Split   : 0
% 2.48/1.69  #Chain   : 0
% 2.48/1.69  #Close   : 0
% 2.48/1.69  
% 2.48/1.69  Ordering : KBO
% 2.48/1.69  
% 2.48/1.69  Simplification rules
% 2.48/1.69  ----------------------
% 2.48/1.69  #Subsume      : 5
% 2.48/1.69  #Demod        : 25
% 2.48/1.69  #Tautology    : 56
% 2.48/1.69  #SimpNegUnit  : 1
% 2.48/1.69  #BackRed      : 0
% 2.48/1.69  
% 2.48/1.69  #Partial instantiations: 0
% 2.48/1.69  #Strategies tried      : 1
% 2.48/1.69  
% 2.48/1.69  Timing (in seconds)
% 2.48/1.69  ----------------------
% 2.62/1.69  Preprocessing        : 0.46
% 2.62/1.69  Parsing              : 0.24
% 2.62/1.69  CNF conversion       : 0.03
% 2.62/1.69  Main loop            : 0.32
% 2.62/1.69  Inferencing          : 0.12
% 2.62/1.69  Reduction            : 0.12
% 2.62/1.69  Demodulation         : 0.09
% 2.62/1.69  BG Simplification    : 0.02
% 2.62/1.69  Subsumption          : 0.05
% 2.62/1.69  Abstraction          : 0.02
% 2.62/1.69  MUC search           : 0.00
% 2.62/1.69  Cooper               : 0.00
% 2.62/1.69  Total                : 0.82
% 2.62/1.70  Index Insertion      : 0.00
% 2.62/1.70  Index Deletion       : 0.00
% 2.62/1.70  Index Matching       : 0.00
% 2.62/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
