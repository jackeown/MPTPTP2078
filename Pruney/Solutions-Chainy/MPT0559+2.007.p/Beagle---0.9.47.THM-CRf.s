%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k7_relat_1(B_8,A_7),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_13,plain,(
    ! [B_13,A_14,C_15] :
      ( r1_tarski(k9_relat_1(B_13,A_14),k9_relat_1(C_15,A_14))
      | ~ r1_tarski(B_13,C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

tff(c_19,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_20,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_19])).

tff(c_23,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_20])).

tff(c_27,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_23])).

tff(c_28,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_19])).

tff(c_32,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_36,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.62/1.11  
% 1.62/1.11  %Foreground sorts:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Background operators:
% 1.62/1.11  
% 1.62/1.11  
% 1.62/1.11  %Foreground operators:
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.62/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.62/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.11  
% 1.62/1.11  tff(f_47, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_relat_1)).
% 1.62/1.11  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.62/1.11  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.62/1.11  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 1.62/1.11  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.11  tff(c_6, plain, (![B_8, A_7]: (r1_tarski(k7_relat_1(B_8, A_7), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.11  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.11  tff(c_13, plain, (![B_13, A_14, C_15]: (r1_tarski(k9_relat_1(B_13, A_14), k9_relat_1(C_15, A_14)) | ~r1_tarski(B_13, C_15) | ~v1_relat_1(C_15) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.11  tff(c_8, plain, (~r1_tarski(k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.11  tff(c_16, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_13, c_8])).
% 1.62/1.11  tff(c_19, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.62/1.11  tff(c_20, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_19])).
% 1.62/1.11  tff(c_23, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_20])).
% 1.62/1.11  tff(c_27, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_23])).
% 1.62/1.11  tff(c_28, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_19])).
% 1.62/1.11  tff(c_32, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.62/1.11  tff(c_36, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 1.62/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  Inference rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Ref     : 0
% 1.62/1.11  #Sup     : 3
% 1.62/1.11  #Fact    : 0
% 1.62/1.11  #Define  : 0
% 1.62/1.11  #Split   : 1
% 1.62/1.11  #Chain   : 0
% 1.62/1.11  #Close   : 0
% 1.62/1.11  
% 1.62/1.11  Ordering : KBO
% 1.62/1.11  
% 1.62/1.11  Simplification rules
% 1.62/1.11  ----------------------
% 1.62/1.11  #Subsume      : 0
% 1.62/1.11  #Demod        : 3
% 1.62/1.11  #Tautology    : 0
% 1.62/1.11  #SimpNegUnit  : 0
% 1.62/1.11  #BackRed      : 0
% 1.62/1.11  
% 1.62/1.11  #Partial instantiations: 0
% 1.62/1.11  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.72/1.12  Preprocessing        : 0.25
% 1.72/1.12  Parsing              : 0.14
% 1.72/1.12  CNF conversion       : 0.01
% 1.72/1.12  Main loop            : 0.08
% 1.72/1.12  Inferencing          : 0.03
% 1.72/1.12  Reduction            : 0.02
% 1.72/1.12  Demodulation         : 0.01
% 1.72/1.12  BG Simplification    : 0.01
% 1.72/1.12  Subsumption          : 0.01
% 1.72/1.12  Abstraction          : 0.00
% 1.72/1.12  MUC search           : 0.00
% 1.72/1.12  Cooper               : 0.00
% 1.72/1.12  Total                : 0.35
% 1.72/1.12  Index Insertion      : 0.00
% 1.72/1.12  Index Deletion       : 0.00
% 1.72/1.12  Index Matching       : 0.00
% 1.72/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
