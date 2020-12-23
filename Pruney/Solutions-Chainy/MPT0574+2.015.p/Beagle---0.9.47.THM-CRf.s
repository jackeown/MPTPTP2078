%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  43 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    ! [B_30,A_31] : k3_tarski(k2_tarski(B_30,A_31)) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_14])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_211,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_232,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_211])).

tff(c_239,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_6,c_232])).

tff(c_377,plain,(
    ! [C_40,A_41,B_42] :
      ( k2_xboole_0(k10_relat_1(C_40,A_41),k10_relat_1(C_40,B_42)) = k10_relat_1(C_40,k2_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_901,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k10_relat_1(C_56,A_57),k10_relat_1(C_56,k2_xboole_0(A_57,B_58)))
      | ~ v1_relat_1(C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_10])).

tff(c_1072,plain,(
    ! [C_61] :
      ( r1_tarski(k10_relat_1(C_61,'#skF_1'),k10_relat_1(C_61,'#skF_2'))
      | ~ v1_relat_1(C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_901])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1078,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1072,c_18])).

tff(c_1083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.61/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.41  
% 2.61/1.42  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.61/1.42  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.61/1.42  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.61/1.42  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.61/1.42  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.61/1.42  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.61/1.42  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.61/1.42  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.61/1.42  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.42  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.42  tff(c_70, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.42  tff(c_129, plain, (![B_30, A_31]: (k3_tarski(k2_tarski(B_30, A_31))=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_12, c_70])).
% 2.61/1.42  tff(c_14, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.42  tff(c_135, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_129, c_14])).
% 2.61/1.42  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.42  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.42  tff(c_85, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.42  tff(c_97, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_85])).
% 2.61/1.42  tff(c_211, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.42  tff(c_232, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_211])).
% 2.61/1.42  tff(c_239, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_6, c_232])).
% 2.61/1.42  tff(c_377, plain, (![C_40, A_41, B_42]: (k2_xboole_0(k10_relat_1(C_40, A_41), k10_relat_1(C_40, B_42))=k10_relat_1(C_40, k2_xboole_0(A_41, B_42)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.42  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.42  tff(c_901, plain, (![C_56, A_57, B_58]: (r1_tarski(k10_relat_1(C_56, A_57), k10_relat_1(C_56, k2_xboole_0(A_57, B_58))) | ~v1_relat_1(C_56))), inference(superposition, [status(thm), theory('equality')], [c_377, c_10])).
% 2.61/1.42  tff(c_1072, plain, (![C_61]: (r1_tarski(k10_relat_1(C_61, '#skF_1'), k10_relat_1(C_61, '#skF_2')) | ~v1_relat_1(C_61))), inference(superposition, [status(thm), theory('equality')], [c_239, c_901])).
% 2.61/1.42  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.42  tff(c_1078, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1072, c_18])).
% 2.61/1.42  tff(c_1083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1078])).
% 2.61/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  Inference rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Ref     : 0
% 2.61/1.42  #Sup     : 268
% 2.61/1.42  #Fact    : 0
% 2.61/1.42  #Define  : 0
% 2.61/1.42  #Split   : 0
% 2.61/1.42  #Chain   : 0
% 2.61/1.42  #Close   : 0
% 2.61/1.42  
% 2.61/1.42  Ordering : KBO
% 2.61/1.42  
% 2.61/1.42  Simplification rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Subsume      : 3
% 2.61/1.42  #Demod        : 194
% 2.61/1.42  #Tautology    : 191
% 2.61/1.42  #SimpNegUnit  : 0
% 2.61/1.42  #BackRed      : 0
% 2.61/1.42  
% 2.61/1.42  #Partial instantiations: 0
% 2.61/1.42  #Strategies tried      : 1
% 2.61/1.42  
% 2.61/1.42  Timing (in seconds)
% 2.61/1.42  ----------------------
% 2.61/1.42  Preprocessing        : 0.28
% 2.61/1.42  Parsing              : 0.16
% 2.61/1.42  CNF conversion       : 0.02
% 2.61/1.42  Main loop            : 0.37
% 2.61/1.42  Inferencing          : 0.14
% 2.61/1.42  Reduction            : 0.15
% 2.61/1.42  Demodulation         : 0.12
% 2.61/1.42  BG Simplification    : 0.02
% 2.61/1.42  Subsumption          : 0.05
% 2.61/1.42  Abstraction          : 0.02
% 2.61/1.42  MUC search           : 0.00
% 2.61/1.42  Cooper               : 0.00
% 2.61/1.42  Total                : 0.68
% 2.61/1.42  Index Insertion      : 0.00
% 2.61/1.42  Index Deletion       : 0.00
% 2.61/1.42  Index Matching       : 0.00
% 2.61/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
