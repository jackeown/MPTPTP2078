%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  59 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [C_18,B_19,A_20] :
      ( k7_relat_1(k7_relat_1(C_18,B_19),A_20) = k7_relat_1(C_18,A_20)
      | ~ r1_tarski(A_20,B_19)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_9,A_8)),k2_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [C_30,A_31,B_32] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_30,A_31)),k2_relat_1(k7_relat_1(C_30,B_32)))
      | ~ v1_relat_1(k7_relat_1(C_30,B_32))
      | ~ r1_tarski(A_31,B_32)
      | ~ v1_relat_1(C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_118,plain,(
    ! [B_36,A_37,A_38] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_36,A_37)),k9_relat_1(B_36,A_38))
      | ~ v1_relat_1(k7_relat_1(B_36,A_38))
      | ~ r1_tarski(A_37,A_38)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_298,plain,(
    ! [B_56,A_57,A_58] :
      ( r1_tarski(k9_relat_1(B_56,A_57),k9_relat_1(B_56,A_58))
      | ~ v1_relat_1(k7_relat_1(B_56,A_58))
      | ~ r1_tarski(A_57,A_58)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_118])).

tff(c_10,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_303,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_10])).

tff(c_313,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_303])).

tff(c_316,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_313])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n013.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 19:08:39 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.09  
% 1.75/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.09  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.09  
% 1.75/1.09  %Foreground sorts:
% 1.75/1.09  
% 1.75/1.09  
% 1.75/1.09  %Background operators:
% 1.75/1.09  
% 1.75/1.09  
% 1.75/1.09  %Foreground operators:
% 1.75/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.75/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.75/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.09  
% 1.75/1.10  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 1.75/1.10  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.75/1.10  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.75/1.10  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 1.75/1.10  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 1.75/1.10  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.10  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.10  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.10  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.75/1.10  tff(c_36, plain, (![C_18, B_19, A_20]: (k7_relat_1(k7_relat_1(C_18, B_19), A_20)=k7_relat_1(C_18, A_20) | ~r1_tarski(A_20, B_19) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.75/1.10  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(k7_relat_1(B_9, A_8)), k2_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.10  tff(c_95, plain, (![C_30, A_31, B_32]: (r1_tarski(k2_relat_1(k7_relat_1(C_30, A_31)), k2_relat_1(k7_relat_1(C_30, B_32))) | ~v1_relat_1(k7_relat_1(C_30, B_32)) | ~r1_tarski(A_31, B_32) | ~v1_relat_1(C_30))), inference(superposition, [status(thm), theory('equality')], [c_36, c_8])).
% 1.75/1.10  tff(c_118, plain, (![B_36, A_37, A_38]: (r1_tarski(k2_relat_1(k7_relat_1(B_36, A_37)), k9_relat_1(B_36, A_38)) | ~v1_relat_1(k7_relat_1(B_36, A_38)) | ~r1_tarski(A_37, A_38) | ~v1_relat_1(B_36) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_95])).
% 1.75/1.10  tff(c_298, plain, (![B_56, A_57, A_58]: (r1_tarski(k9_relat_1(B_56, A_57), k9_relat_1(B_56, A_58)) | ~v1_relat_1(k7_relat_1(B_56, A_58)) | ~r1_tarski(A_57, A_58) | ~v1_relat_1(B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_6, c_118])).
% 1.75/1.10  tff(c_10, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.10  tff(c_303, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_10])).
% 1.75/1.10  tff(c_313, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_303])).
% 1.75/1.10  tff(c_316, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_313])).
% 1.75/1.10  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_316])).
% 1.75/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.10  
% 1.75/1.10  Inference rules
% 1.75/1.10  ----------------------
% 1.75/1.10  #Ref     : 0
% 1.75/1.10  #Sup     : 87
% 1.75/1.10  #Fact    : 0
% 1.75/1.10  #Define  : 0
% 1.75/1.10  #Split   : 0
% 1.75/1.10  #Chain   : 0
% 1.75/1.10  #Close   : 0
% 1.75/1.10  
% 1.75/1.10  Ordering : KBO
% 1.75/1.10  
% 1.75/1.10  Simplification rules
% 1.75/1.10  ----------------------
% 1.75/1.10  #Subsume      : 8
% 1.75/1.10  #Demod        : 3
% 1.75/1.10  #Tautology    : 10
% 1.75/1.10  #SimpNegUnit  : 0
% 1.75/1.10  #BackRed      : 0
% 1.75/1.10  
% 1.75/1.10  #Partial instantiations: 0
% 1.75/1.10  #Strategies tried      : 1
% 1.75/1.10  
% 1.75/1.10  Timing (in seconds)
% 1.75/1.10  ----------------------
% 1.75/1.11  Preprocessing        : 0.26
% 1.75/1.11  Parsing              : 0.15
% 1.75/1.11  CNF conversion       : 0.02
% 1.75/1.11  Main loop            : 0.25
% 1.75/1.11  Inferencing          : 0.11
% 1.75/1.11  Reduction            : 0.06
% 1.75/1.11  Demodulation         : 0.04
% 1.75/1.11  BG Simplification    : 0.02
% 1.75/1.11  Subsumption          : 0.06
% 1.75/1.11  Abstraction          : 0.01
% 1.75/1.11  MUC search           : 0.00
% 1.75/1.11  Cooper               : 0.00
% 1.75/1.11  Total                : 0.54
% 1.75/1.11  Index Insertion      : 0.00
% 1.75/1.11  Index Deletion       : 0.00
% 1.75/1.11  Index Matching       : 0.00
% 1.75/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
