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
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   28 (  41 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  64 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k8_relat_1(A_3,B_4),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    ! [B_13,A_14,C_15] :
      ( r1_tarski(k9_relat_1(B_13,A_14),k9_relat_1(C_15,A_14))
      | ~ r1_tarski(B_13,C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_15,c_8])).

tff(c_21,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_22,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21])).

tff(c_25,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_29,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25])).

tff(c_30,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_21])).

tff(c_34,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:55:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.18  
% 1.67/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.19  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.67/1.19  
% 1.67/1.19  %Foreground sorts:
% 1.67/1.19  
% 1.67/1.19  
% 1.67/1.19  %Background operators:
% 1.67/1.19  
% 1.67/1.19  
% 1.67/1.19  %Foreground operators:
% 1.67/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.67/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.67/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.19  
% 1.67/1.20  tff(f_49, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_funct_1)).
% 1.67/1.20  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.67/1.20  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.67/1.20  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 1.67/1.20  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.20  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.20  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.20  tff(c_15, plain, (![B_13, A_14, C_15]: (r1_tarski(k9_relat_1(B_13, A_14), k9_relat_1(C_15, A_14)) | ~r1_tarski(B_13, C_15) | ~v1_relat_1(C_15) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.20  tff(c_8, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.20  tff(c_18, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_15, c_8])).
% 1.67/1.20  tff(c_21, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 1.67/1.20  tff(c_22, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_21])).
% 1.67/1.20  tff(c_25, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.67/1.20  tff(c_29, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_25])).
% 1.67/1.20  tff(c_30, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_21])).
% 1.67/1.20  tff(c_34, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_30])).
% 1.67/1.20  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.67/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.20  
% 1.67/1.20  Inference rules
% 1.67/1.20  ----------------------
% 1.67/1.20  #Ref     : 0
% 1.67/1.20  #Sup     : 3
% 1.67/1.20  #Fact    : 0
% 1.67/1.20  #Define  : 0
% 1.67/1.20  #Split   : 1
% 1.67/1.20  #Chain   : 0
% 1.67/1.20  #Close   : 0
% 1.67/1.20  
% 1.67/1.20  Ordering : KBO
% 1.67/1.20  
% 1.67/1.20  Simplification rules
% 1.67/1.20  ----------------------
% 1.67/1.20  #Subsume      : 0
% 1.67/1.20  #Demod        : 3
% 1.67/1.20  #Tautology    : 0
% 1.67/1.20  #SimpNegUnit  : 0
% 1.67/1.20  #BackRed      : 0
% 1.67/1.20  
% 1.67/1.20  #Partial instantiations: 0
% 1.67/1.20  #Strategies tried      : 1
% 1.67/1.20  
% 1.67/1.20  Timing (in seconds)
% 1.67/1.20  ----------------------
% 1.67/1.20  Preprocessing        : 0.23
% 1.67/1.20  Parsing              : 0.13
% 1.67/1.20  CNF conversion       : 0.02
% 1.67/1.20  Main loop            : 0.12
% 1.67/1.20  Inferencing          : 0.04
% 1.67/1.20  Reduction            : 0.03
% 1.67/1.20  Demodulation         : 0.02
% 1.67/1.20  BG Simplification    : 0.01
% 1.67/1.20  Subsumption          : 0.02
% 1.67/1.20  Abstraction          : 0.00
% 1.67/1.20  MUC search           : 0.00
% 1.67/1.20  Cooper               : 0.00
% 1.67/1.20  Total                : 0.39
% 1.67/1.20  Index Insertion      : 0.00
% 1.67/1.20  Index Deletion       : 0.00
% 1.67/1.20  Index Matching       : 0.00
% 1.67/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
