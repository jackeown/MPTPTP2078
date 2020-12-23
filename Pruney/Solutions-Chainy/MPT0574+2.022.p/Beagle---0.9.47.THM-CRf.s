%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [C_23,A_24,B_25] :
      ( r1_tarski(k10_relat_1(C_23,k3_xboole_0(A_24,B_25)),k3_xboole_0(k10_relat_1(C_23,A_24),k10_relat_1(C_23,B_25)))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [C_26,A_27,B_28] :
      ( r1_tarski(k10_relat_1(C_26,k3_xboole_0(A_27,B_28)),k10_relat_1(C_26,A_27))
      | ~ v1_relat_1(C_26) ) ),
    inference(resolution,[status(thm)],[c_83,c_4])).

tff(c_131,plain,(
    ! [C_30,A_31,B_32] :
      ( r1_tarski(k10_relat_1(C_30,k3_xboole_0(A_31,B_32)),k10_relat_1(C_30,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_175,plain,(
    ! [C_36] :
      ( r1_tarski(k10_relat_1(C_36,'#skF_1'),k10_relat_1(C_36,'#skF_2'))
      | ~ v1_relat_1(C_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_131])).

tff(c_10,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_178,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_10])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.48  
% 2.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.48  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.15/1.48  
% 2.15/1.48  %Foreground sorts:
% 2.15/1.48  
% 2.15/1.48  
% 2.15/1.48  %Background operators:
% 2.15/1.48  
% 2.15/1.48  
% 2.15/1.48  %Foreground operators:
% 2.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.15/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.48  
% 2.15/1.50  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 2.15/1.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.15/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.15/1.50  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.15/1.50  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.15/1.50  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.50  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.50  tff(c_48, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.50  tff(c_52, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_48])).
% 2.15/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.50  tff(c_83, plain, (![C_23, A_24, B_25]: (r1_tarski(k10_relat_1(C_23, k3_xboole_0(A_24, B_25)), k3_xboole_0(k10_relat_1(C_23, A_24), k10_relat_1(C_23, B_25))) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.50  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.50  tff(c_111, plain, (![C_26, A_27, B_28]: (r1_tarski(k10_relat_1(C_26, k3_xboole_0(A_27, B_28)), k10_relat_1(C_26, A_27)) | ~v1_relat_1(C_26))), inference(resolution, [status(thm)], [c_83, c_4])).
% 2.15/1.50  tff(c_131, plain, (![C_30, A_31, B_32]: (r1_tarski(k10_relat_1(C_30, k3_xboole_0(A_31, B_32)), k10_relat_1(C_30, B_32)) | ~v1_relat_1(C_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_111])).
% 2.15/1.50  tff(c_175, plain, (![C_36]: (r1_tarski(k10_relat_1(C_36, '#skF_1'), k10_relat_1(C_36, '#skF_2')) | ~v1_relat_1(C_36))), inference(superposition, [status(thm), theory('equality')], [c_52, c_131])).
% 2.15/1.50  tff(c_10, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.15/1.50  tff(c_178, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_175, c_10])).
% 2.15/1.50  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_178])).
% 2.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.50  
% 2.15/1.50  Inference rules
% 2.15/1.50  ----------------------
% 2.15/1.50  #Ref     : 0
% 2.15/1.50  #Sup     : 45
% 2.15/1.50  #Fact    : 0
% 2.15/1.50  #Define  : 0
% 2.15/1.50  #Split   : 0
% 2.15/1.50  #Chain   : 0
% 2.15/1.50  #Close   : 0
% 2.15/1.50  
% 2.15/1.50  Ordering : KBO
% 2.15/1.50  
% 2.15/1.50  Simplification rules
% 2.15/1.50  ----------------------
% 2.15/1.50  #Subsume      : 11
% 2.15/1.50  #Demod        : 4
% 2.15/1.50  #Tautology    : 11
% 2.15/1.50  #SimpNegUnit  : 0
% 2.15/1.50  #BackRed      : 0
% 2.15/1.50  
% 2.15/1.50  #Partial instantiations: 0
% 2.15/1.50  #Strategies tried      : 1
% 2.15/1.50  
% 2.15/1.50  Timing (in seconds)
% 2.15/1.50  ----------------------
% 2.15/1.50  Preprocessing        : 0.38
% 2.15/1.50  Parsing              : 0.20
% 2.15/1.50  CNF conversion       : 0.02
% 2.15/1.50  Main loop            : 0.25
% 2.15/1.50  Inferencing          : 0.10
% 2.15/1.50  Reduction            : 0.07
% 2.15/1.50  Demodulation         : 0.06
% 2.15/1.50  BG Simplification    : 0.01
% 2.15/1.50  Subsumption          : 0.05
% 2.15/1.50  Abstraction          : 0.01
% 2.15/1.50  MUC search           : 0.00
% 2.15/1.50  Cooper               : 0.00
% 2.15/1.50  Total                : 0.67
% 2.15/1.50  Index Insertion      : 0.00
% 2.15/1.50  Index Deletion       : 0.00
% 2.15/1.50  Index Matching       : 0.00
% 2.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
