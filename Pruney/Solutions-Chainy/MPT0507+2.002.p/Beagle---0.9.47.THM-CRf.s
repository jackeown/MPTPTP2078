%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    ! [C_15,A_16,B_17] :
      ( r1_tarski(k5_relat_1(C_15,A_16),k5_relat_1(C_15,B_17))
      | ~ r1_tarski(A_16,B_17)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [B_10,A_9,B_17] :
      ( r1_tarski(k7_relat_1(B_10,A_9),k5_relat_1(k6_relat_1(A_9),B_17))
      | ~ r1_tarski(B_10,B_17)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_25])).

tff(c_36,plain,(
    ! [B_18,A_19,B_20] :
      ( r1_tarski(k7_relat_1(B_18,A_19),k5_relat_1(k6_relat_1(A_19),B_20))
      | ~ r1_tarski(B_18,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_44,plain,(
    ! [B_24,A_25,B_26] :
      ( r1_tarski(k7_relat_1(B_24,A_25),k7_relat_1(B_26,A_25))
      | ~ r1_tarski(B_24,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_8,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_10,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.10  
% 1.68/1.10  %Foreground sorts:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Background operators:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Foreground operators:
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.10  
% 1.68/1.11  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 1.68/1.11  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.68/1.11  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.68/1.11  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 1.68/1.11  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_10, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_6, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.68/1.11  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.11  tff(c_25, plain, (![C_15, A_16, B_17]: (r1_tarski(k5_relat_1(C_15, A_16), k5_relat_1(C_15, B_17)) | ~r1_tarski(A_16, B_17) | ~v1_relat_1(C_15) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.11  tff(c_28, plain, (![B_10, A_9, B_17]: (r1_tarski(k7_relat_1(B_10, A_9), k5_relat_1(k6_relat_1(A_9), B_17)) | ~r1_tarski(B_10, B_17) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(B_17) | ~v1_relat_1(B_10) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_6, c_25])).
% 1.68/1.11  tff(c_36, plain, (![B_18, A_19, B_20]: (r1_tarski(k7_relat_1(B_18, A_19), k5_relat_1(k6_relat_1(A_19), B_20)) | ~r1_tarski(B_18, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.68/1.11  tff(c_44, plain, (![B_24, A_25, B_26]: (r1_tarski(k7_relat_1(B_24, A_25), k7_relat_1(B_26, A_25)) | ~r1_tarski(B_24, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(B_24) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_6, c_36])).
% 1.68/1.11  tff(c_8, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_47, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_8])).
% 1.68/1.11  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_10, c_47])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.11  #Sup     : 7
% 1.68/1.11  #Fact    : 0
% 1.68/1.11  #Define  : 0
% 1.68/1.11  #Split   : 0
% 1.68/1.11  #Chain   : 0
% 1.68/1.11  #Close   : 0
% 1.68/1.11  
% 1.68/1.11  Ordering : KBO
% 1.68/1.11  
% 1.68/1.11  Simplification rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Subsume      : 0
% 1.68/1.11  #Demod        : 5
% 1.68/1.11  #Tautology    : 2
% 1.68/1.11  #SimpNegUnit  : 0
% 1.68/1.11  #BackRed      : 0
% 1.68/1.11  
% 1.68/1.11  #Partial instantiations: 0
% 1.68/1.11  #Strategies tried      : 1
% 1.68/1.11  
% 1.68/1.11  Timing (in seconds)
% 1.68/1.11  ----------------------
% 1.68/1.11  Preprocessing        : 0.25
% 1.68/1.11  Parsing              : 0.14
% 1.68/1.11  CNF conversion       : 0.02
% 1.68/1.11  Main loop            : 0.09
% 1.68/1.11  Inferencing          : 0.04
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.01
% 1.68/1.12  Abstraction          : 0.00
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.37
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
