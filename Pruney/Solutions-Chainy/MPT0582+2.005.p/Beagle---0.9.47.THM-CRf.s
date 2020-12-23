%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:58 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  63 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15,plain,(
    ! [B_8,A_9] :
      ( k7_relat_1(B_8,A_9) = B_8
      | ~ r1_tarski(k1_relat_1(B_8),A_9)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_21,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_26,plain,(
    ! [B_10,A_11,C_12] :
      ( r1_tarski(k7_relat_1(B_10,A_11),k7_relat_1(C_12,A_11))
      | ~ r1_tarski(B_10,C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29,plain,(
    ! [C_12] :
      ( r1_tarski('#skF_3',k7_relat_1(C_12,'#skF_1'))
      | ~ r1_tarski('#skF_3',C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_26])).

tff(c_37,plain,(
    ! [C_13] :
      ( r1_tarski('#skF_3',k7_relat_1(C_13,'#skF_1'))
      | ~ r1_tarski('#skF_3',C_13)
      | ~ v1_relat_1(C_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_6,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_6])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.09  
% 1.61/1.09  %Foreground sorts:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Background operators:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Foreground operators:
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.09  
% 1.61/1.10  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 1.61/1.10  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.10  tff(f_34, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 1.61/1.10  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.10  tff(c_8, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.10  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.10  tff(c_10, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.10  tff(c_15, plain, (![B_8, A_9]: (k7_relat_1(B_8, A_9)=B_8 | ~r1_tarski(k1_relat_1(B_8), A_9) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.10  tff(c_18, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.61/1.10  tff(c_21, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 1.61/1.10  tff(c_26, plain, (![B_10, A_11, C_12]: (r1_tarski(k7_relat_1(B_10, A_11), k7_relat_1(C_12, A_11)) | ~r1_tarski(B_10, C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.10  tff(c_29, plain, (![C_12]: (r1_tarski('#skF_3', k7_relat_1(C_12, '#skF_1')) | ~r1_tarski('#skF_3', C_12) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21, c_26])).
% 1.61/1.10  tff(c_37, plain, (![C_13]: (r1_tarski('#skF_3', k7_relat_1(C_13, '#skF_1')) | ~r1_tarski('#skF_3', C_13) | ~v1_relat_1(C_13))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_29])).
% 1.61/1.10  tff(c_6, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.61/1.10  tff(c_40, plain, (~r1_tarski('#skF_3', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_37, c_6])).
% 1.61/1.10  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_8, c_40])).
% 1.61/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  Inference rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Ref     : 0
% 1.61/1.10  #Sup     : 7
% 1.61/1.10  #Fact    : 0
% 1.61/1.10  #Define  : 0
% 1.61/1.10  #Split   : 0
% 1.61/1.10  #Chain   : 0
% 1.61/1.10  #Close   : 0
% 1.61/1.10  
% 1.61/1.10  Ordering : KBO
% 1.61/1.10  
% 1.61/1.10  Simplification rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Subsume      : 0
% 1.61/1.10  #Demod        : 5
% 1.61/1.10  #Tautology    : 2
% 1.61/1.10  #SimpNegUnit  : 0
% 1.61/1.10  #BackRed      : 0
% 1.61/1.10  
% 1.61/1.10  #Partial instantiations: 0
% 1.61/1.10  #Strategies tried      : 1
% 1.61/1.10  
% 1.61/1.10  Timing (in seconds)
% 1.61/1.10  ----------------------
% 1.61/1.10  Preprocessing        : 0.25
% 1.61/1.10  Parsing              : 0.14
% 1.61/1.10  CNF conversion       : 0.02
% 1.61/1.10  Main loop            : 0.09
% 1.61/1.10  Inferencing          : 0.04
% 1.61/1.10  Reduction            : 0.02
% 1.61/1.10  Demodulation         : 0.02
% 1.61/1.10  BG Simplification    : 0.01
% 1.61/1.10  Subsumption          : 0.01
% 1.61/1.10  Abstraction          : 0.00
% 1.61/1.10  MUC search           : 0.00
% 1.61/1.10  Cooper               : 0.00
% 1.61/1.10  Total                : 0.36
% 1.61/1.10  Index Insertion      : 0.00
% 1.61/1.10  Index Deletion       : 0.00
% 1.61/1.10  Index Matching       : 0.00
% 1.61/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
