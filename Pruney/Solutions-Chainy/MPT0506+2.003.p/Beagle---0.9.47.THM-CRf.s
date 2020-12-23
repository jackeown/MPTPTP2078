%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.05s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
         => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    ! [C_12,B_13,A_14] :
      ( k7_relat_1(k7_relat_1(C_12,B_13),A_14) = k7_relat_1(C_12,A_14)
      | ~ r1_tarski(A_14,B_13)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k7_relat_1(B_7,A_6),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [C_15,A_16,B_17] :
      ( r1_tarski(k7_relat_1(C_15,A_16),k7_relat_1(C_15,B_17))
      | ~ v1_relat_1(k7_relat_1(C_15,B_17))
      | ~ r1_tarski(A_16,B_17)
      | ~ v1_relat_1(C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_6])).

tff(c_8,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_8])).

tff(c_48,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_39])).

tff(c_51,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:45:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.49  
% 1.97/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.50  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.97/1.50  
% 1.97/1.50  %Foreground sorts:
% 1.97/1.50  
% 1.97/1.50  
% 1.97/1.50  %Background operators:
% 1.97/1.50  
% 1.97/1.50  
% 1.97/1.50  %Foreground operators:
% 1.97/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.50  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.50  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.50  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.50  
% 2.05/1.52  tff(f_46, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_relat_1)).
% 2.05/1.52  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.05/1.52  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.05/1.52  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.05/1.52  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.52  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.52  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.52  tff(c_15, plain, (![C_12, B_13, A_14]: (k7_relat_1(k7_relat_1(C_12, B_13), A_14)=k7_relat_1(C_12, A_14) | ~r1_tarski(A_14, B_13) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.52  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k7_relat_1(B_7, A_6), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.52  tff(c_36, plain, (![C_15, A_16, B_17]: (r1_tarski(k7_relat_1(C_15, A_16), k7_relat_1(C_15, B_17)) | ~v1_relat_1(k7_relat_1(C_15, B_17)) | ~r1_tarski(A_16, B_17) | ~v1_relat_1(C_15))), inference(superposition, [status(thm), theory('equality')], [c_15, c_6])).
% 2.05/1.52  tff(c_8, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.52  tff(c_39, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_8])).
% 2.05/1.52  tff(c_48, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_39])).
% 2.05/1.52  tff(c_51, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_48])).
% 2.05/1.52  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_51])).
% 2.05/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.52  
% 2.05/1.52  Inference rules
% 2.05/1.52  ----------------------
% 2.05/1.52  #Ref     : 0
% 2.05/1.52  #Sup     : 10
% 2.05/1.52  #Fact    : 0
% 2.05/1.52  #Define  : 0
% 2.05/1.52  #Split   : 0
% 2.05/1.52  #Chain   : 0
% 2.05/1.52  #Close   : 0
% 2.05/1.52  
% 2.05/1.52  Ordering : KBO
% 2.05/1.52  
% 2.05/1.52  Simplification rules
% 2.05/1.52  ----------------------
% 2.05/1.52  #Subsume      : 1
% 2.05/1.52  #Demod        : 3
% 2.05/1.52  #Tautology    : 2
% 2.05/1.52  #SimpNegUnit  : 0
% 2.05/1.52  #BackRed      : 0
% 2.05/1.52  
% 2.05/1.52  #Partial instantiations: 0
% 2.05/1.52  #Strategies tried      : 1
% 2.05/1.52  
% 2.05/1.52  Timing (in seconds)
% 2.05/1.52  ----------------------
% 2.05/1.52  Preprocessing        : 0.40
% 2.05/1.52  Parsing              : 0.21
% 2.05/1.52  CNF conversion       : 0.03
% 2.05/1.52  Main loop            : 0.16
% 2.05/1.52  Inferencing          : 0.07
% 2.05/1.52  Reduction            : 0.04
% 2.05/1.52  Demodulation         : 0.03
% 2.05/1.52  BG Simplification    : 0.01
% 2.05/1.52  Subsumption          : 0.03
% 2.05/1.52  Abstraction          : 0.01
% 2.05/1.52  MUC search           : 0.00
% 2.05/1.52  Cooper               : 0.00
% 2.05/1.52  Total                : 0.60
% 2.05/1.52  Index Insertion      : 0.00
% 2.05/1.52  Index Deletion       : 0.00
% 2.05/1.52  Index Matching       : 0.00
% 2.05/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
