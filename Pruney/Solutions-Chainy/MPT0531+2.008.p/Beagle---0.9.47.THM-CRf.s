%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    ! [A_12,B_13,C_14] :
      ( k8_relat_1(A_12,k8_relat_1(B_13,C_14)) = k8_relat_1(A_12,C_14)
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k8_relat_1(A_3,B_4),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(k8_relat_1(A_15,C_16),k8_relat_1(B_17,C_16))
      | ~ v1_relat_1(k8_relat_1(B_17,C_16))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(C_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_4])).

tff(c_8,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_8])).

tff(c_48,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_39])).

tff(c_51,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:42:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.49  
% 1.95/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.50  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.95/1.50  
% 1.95/1.50  %Foreground sorts:
% 1.95/1.50  
% 1.95/1.50  
% 1.95/1.50  %Background operators:
% 1.95/1.50  
% 1.95/1.50  
% 1.95/1.50  %Foreground operators:
% 1.95/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.95/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.50  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.50  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.50  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.50  
% 1.95/1.51  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 1.95/1.51  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.95/1.51  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 1.95/1.51  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.95/1.51  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.51  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.51  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.51  tff(c_15, plain, (![A_12, B_13, C_14]: (k8_relat_1(A_12, k8_relat_1(B_13, C_14))=k8_relat_1(A_12, C_14) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.51  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.51  tff(c_36, plain, (![A_15, C_16, B_17]: (r1_tarski(k8_relat_1(A_15, C_16), k8_relat_1(B_17, C_16)) | ~v1_relat_1(k8_relat_1(B_17, C_16)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(C_16))), inference(superposition, [status(thm), theory('equality')], [c_15, c_4])).
% 1.95/1.51  tff(c_8, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.51  tff(c_39, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_8])).
% 1.95/1.51  tff(c_48, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_39])).
% 1.95/1.51  tff(c_51, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_48])).
% 1.95/1.51  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_51])).
% 1.95/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.51  
% 1.95/1.51  Inference rules
% 1.95/1.51  ----------------------
% 1.95/1.51  #Ref     : 0
% 1.95/1.51  #Sup     : 10
% 1.95/1.51  #Fact    : 0
% 1.95/1.51  #Define  : 0
% 1.95/1.51  #Split   : 0
% 1.95/1.51  #Chain   : 0
% 1.95/1.51  #Close   : 0
% 1.95/1.51  
% 1.95/1.51  Ordering : KBO
% 1.95/1.51  
% 1.95/1.51  Simplification rules
% 1.95/1.51  ----------------------
% 1.95/1.51  #Subsume      : 1
% 1.95/1.51  #Demod        : 3
% 1.95/1.51  #Tautology    : 2
% 1.95/1.51  #SimpNegUnit  : 0
% 1.95/1.51  #BackRed      : 0
% 1.95/1.51  
% 1.95/1.51  #Partial instantiations: 0
% 1.95/1.51  #Strategies tried      : 1
% 1.95/1.51  
% 1.95/1.51  Timing (in seconds)
% 1.95/1.51  ----------------------
% 1.95/1.52  Preprocessing        : 0.38
% 1.95/1.52  Parsing              : 0.21
% 1.95/1.52  CNF conversion       : 0.03
% 1.95/1.52  Main loop            : 0.15
% 1.95/1.52  Inferencing          : 0.07
% 1.95/1.52  Reduction            : 0.04
% 1.95/1.52  Demodulation         : 0.03
% 1.95/1.52  BG Simplification    : 0.01
% 1.95/1.52  Subsumption          : 0.03
% 1.95/1.52  Abstraction          : 0.01
% 1.95/1.52  MUC search           : 0.00
% 1.95/1.52  Cooper               : 0.00
% 1.95/1.52  Total                : 0.58
% 1.95/1.52  Index Insertion      : 0.00
% 1.95/1.52  Index Deletion       : 0.00
% 1.95/1.52  Index Matching       : 0.00
% 1.95/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
