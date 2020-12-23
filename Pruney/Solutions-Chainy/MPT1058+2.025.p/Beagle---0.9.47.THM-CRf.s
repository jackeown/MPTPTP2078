%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  37 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_22,C_23,B_24] :
      ( k3_xboole_0(A_22,k10_relat_1(C_23,B_24)) = k10_relat_1(k7_relat_1(C_23,A_22),B_24)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [B_18,A_19] : k1_setfam_1(k2_tarski(B_18,A_19)) = k3_xboole_0(A_19,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_55])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,A_19) = k3_xboole_0(A_19,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_130,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_76])).

tff(c_155,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_130])).

tff(c_178,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:11:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.68/1.13  
% 1.68/1.14  tff(f_47, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 1.68/1.14  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 1.68/1.14  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.68/1.14  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.68/1.14  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.68/1.14  tff(c_10, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.14  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.14  tff(c_149, plain, (![A_22, C_23, B_24]: (k3_xboole_0(A_22, k10_relat_1(C_23, B_24))=k10_relat_1(k7_relat_1(C_23, A_22), B_24) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.68/1.14  tff(c_12, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.14  tff(c_50, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.14  tff(c_54, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_50])).
% 1.68/1.14  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.14  tff(c_55, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.14  tff(c_70, plain, (![B_18, A_19]: (k1_setfam_1(k2_tarski(B_18, A_19))=k3_xboole_0(A_19, B_18))), inference(superposition, [status(thm), theory('equality')], [c_4, c_55])).
% 1.68/1.14  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.14  tff(c_76, plain, (![B_18, A_19]: (k3_xboole_0(B_18, A_19)=k3_xboole_0(A_19, B_18))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 1.68/1.14  tff(c_130, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54, c_76])).
% 1.68/1.14  tff(c_155, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_149, c_130])).
% 1.68/1.14  tff(c_178, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_155])).
% 1.68/1.14  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_178])).
% 1.68/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  Inference rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Ref     : 0
% 1.68/1.14  #Sup     : 43
% 1.68/1.14  #Fact    : 0
% 1.68/1.14  #Define  : 0
% 1.68/1.14  #Split   : 0
% 1.68/1.14  #Chain   : 0
% 1.68/1.14  #Close   : 0
% 1.68/1.14  
% 1.68/1.14  Ordering : KBO
% 1.68/1.14  
% 1.68/1.14  Simplification rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Subsume      : 1
% 1.68/1.14  #Demod        : 6
% 1.68/1.14  #Tautology    : 30
% 1.68/1.14  #SimpNegUnit  : 1
% 1.68/1.14  #BackRed      : 0
% 1.68/1.14  
% 1.68/1.14  #Partial instantiations: 0
% 1.68/1.14  #Strategies tried      : 1
% 1.68/1.14  
% 1.68/1.14  Timing (in seconds)
% 1.68/1.14  ----------------------
% 1.68/1.15  Preprocessing        : 0.28
% 1.68/1.15  Parsing              : 0.15
% 1.68/1.15  CNF conversion       : 0.02
% 1.68/1.15  Main loop            : 0.12
% 1.68/1.15  Inferencing          : 0.05
% 1.68/1.15  Reduction            : 0.04
% 1.68/1.15  Demodulation         : 0.04
% 1.68/1.15  BG Simplification    : 0.01
% 1.68/1.15  Subsumption          : 0.02
% 1.68/1.15  Abstraction          : 0.01
% 1.68/1.15  MUC search           : 0.00
% 1.68/1.15  Cooper               : 0.00
% 1.68/1.15  Total                : 0.43
% 1.68/1.15  Index Insertion      : 0.00
% 1.68/1.15  Index Deletion       : 0.00
% 1.68/1.15  Index Matching       : 0.00
% 1.68/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
