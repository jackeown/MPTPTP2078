%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k8_relat_1(A_6,B_7),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_23,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,'#skF_4')
      | ~ r1_tarski(A_23,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_37,plain,(
    ! [A_6] :
      ( r1_tarski(k8_relat_1(A_6,'#skF_3'),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_40,plain,(
    ! [A_6] : r1_tarski(k8_relat_1(A_6,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_8,plain,(
    ! [B_9,A_8,C_10] :
      ( k8_relat_1(B_9,k8_relat_1(A_8,C_10)) = k8_relat_1(A_8,C_10)
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k8_relat_1(A_46,B_47),k8_relat_1(A_46,C_48))
      | ~ r1_tarski(B_47,C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1702,plain,(
    ! [A_129,C_130,B_131,C_132] :
      ( r1_tarski(k8_relat_1(A_129,C_130),k8_relat_1(B_131,C_132))
      | ~ r1_tarski(k8_relat_1(A_129,C_130),C_132)
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(k8_relat_1(A_129,C_130))
      | ~ r1_tarski(A_129,B_131)
      | ~ v1_relat_1(C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_170])).

tff(c_12,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1745,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1702,c_12])).

tff(c_1791,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_18,c_40,c_1745])).

tff(c_1794,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1791])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.73  
% 3.96/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.73  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.96/1.73  
% 3.96/1.73  %Foreground sorts:
% 3.96/1.73  
% 3.96/1.73  
% 3.96/1.73  %Background operators:
% 3.96/1.73  
% 3.96/1.73  
% 3.96/1.73  %Foreground operators:
% 3.96/1.73  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.96/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.73  
% 3.96/1.74  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 3.96/1.74  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.96/1.74  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 3.96/1.74  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.96/1.74  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 3.96/1.74  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 3.96/1.74  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.74  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.74  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.74  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.74  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k8_relat_1(A_6, B_7), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.74  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.74  tff(c_23, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.74  tff(c_33, plain, (![A_23]: (r1_tarski(A_23, '#skF_4') | ~r1_tarski(A_23, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_23])).
% 3.96/1.74  tff(c_37, plain, (![A_6]: (r1_tarski(k8_relat_1(A_6, '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_33])).
% 3.96/1.74  tff(c_40, plain, (![A_6]: (r1_tarski(k8_relat_1(A_6, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37])).
% 3.96/1.74  tff(c_8, plain, (![B_9, A_8, C_10]: (k8_relat_1(B_9, k8_relat_1(A_8, C_10))=k8_relat_1(A_8, C_10) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.96/1.74  tff(c_170, plain, (![A_46, B_47, C_48]: (r1_tarski(k8_relat_1(A_46, B_47), k8_relat_1(A_46, C_48)) | ~r1_tarski(B_47, C_48) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.96/1.74  tff(c_1702, plain, (![A_129, C_130, B_131, C_132]: (r1_tarski(k8_relat_1(A_129, C_130), k8_relat_1(B_131, C_132)) | ~r1_tarski(k8_relat_1(A_129, C_130), C_132) | ~v1_relat_1(C_132) | ~v1_relat_1(k8_relat_1(A_129, C_130)) | ~r1_tarski(A_129, B_131) | ~v1_relat_1(C_130))), inference(superposition, [status(thm), theory('equality')], [c_8, c_170])).
% 3.96/1.74  tff(c_12, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.96/1.74  tff(c_1745, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1702, c_12])).
% 3.96/1.74  tff(c_1791, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_18, c_40, c_1745])).
% 3.96/1.74  tff(c_1794, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1791])).
% 3.96/1.74  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1794])).
% 3.96/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.74  
% 3.96/1.74  Inference rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Ref     : 0
% 3.96/1.74  #Sup     : 453
% 3.96/1.74  #Fact    : 0
% 3.96/1.74  #Define  : 0
% 3.96/1.74  #Split   : 6
% 3.96/1.74  #Chain   : 0
% 3.96/1.74  #Close   : 0
% 3.96/1.74  
% 3.96/1.74  Ordering : KBO
% 3.96/1.74  
% 3.96/1.74  Simplification rules
% 3.96/1.74  ----------------------
% 3.96/1.74  #Subsume      : 166
% 3.96/1.74  #Demod        : 137
% 3.96/1.74  #Tautology    : 33
% 3.96/1.74  #SimpNegUnit  : 0
% 3.96/1.74  #BackRed      : 0
% 3.96/1.74  
% 3.96/1.74  #Partial instantiations: 0
% 3.96/1.74  #Strategies tried      : 1
% 3.96/1.74  
% 3.96/1.74  Timing (in seconds)
% 3.96/1.74  ----------------------
% 3.96/1.74  Preprocessing        : 0.29
% 3.96/1.74  Parsing              : 0.16
% 3.96/1.74  CNF conversion       : 0.02
% 3.96/1.74  Main loop            : 0.65
% 3.96/1.74  Inferencing          : 0.21
% 3.96/1.74  Reduction            : 0.17
% 3.96/1.74  Demodulation         : 0.11
% 3.96/1.74  BG Simplification    : 0.03
% 3.96/1.74  Subsumption          : 0.21
% 3.96/1.74  Abstraction          : 0.03
% 3.96/1.74  MUC search           : 0.00
% 3.96/1.74  Cooper               : 0.00
% 3.96/1.74  Total                : 0.97
% 3.96/1.74  Index Insertion      : 0.00
% 3.96/1.74  Index Deletion       : 0.00
% 3.96/1.74  Index Matching       : 0.00
% 3.96/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
