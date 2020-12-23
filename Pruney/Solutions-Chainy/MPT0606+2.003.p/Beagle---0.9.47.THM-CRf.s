%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:28 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  78 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => ( r1_tarski(C,B)
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t210_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( ( r1_tarski(k1_relat_1(C),A)
              & r1_tarski(C,B) )
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [B_12,A_13] :
      ( k7_relat_1(B_12,A_13) = B_12
      | ~ v4_relat_1(B_12,A_13)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_24,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_8,A_7)),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_32,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_34,plain,(
    ! [C_14,B_15,A_16] :
      ( r1_tarski(C_14,k7_relat_1(B_15,A_16))
      | ~ r1_tarski(C_14,B_15)
      | ~ r1_tarski(k1_relat_1(C_14),A_16)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [B_15] :
      ( r1_tarski('#skF_3',k7_relat_1(B_15,'#skF_1'))
      | ~ r1_tarski('#skF_3',B_15)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_43,plain,(
    ! [B_17] :
      ( r1_tarski('#skF_3',k7_relat_1(B_17,'#skF_1'))
      | ~ r1_tarski('#skF_3',B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_8,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.66/1.12  
% 1.66/1.12  %Foreground sorts:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Background operators:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Foreground operators:
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.66/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.12  
% 1.66/1.13  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => (r1_tarski(C, B) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t210_relat_1)).
% 1.66/1.13  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.66/1.13  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.66/1.13  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 1.66/1.13  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.13  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.13  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.13  tff(c_12, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.13  tff(c_18, plain, (![B_12, A_13]: (k7_relat_1(B_12, A_13)=B_12 | ~v4_relat_1(B_12, A_13) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.13  tff(c_21, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.66/1.13  tff(c_24, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21])).
% 1.66/1.13  tff(c_6, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_8, A_7)), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.13  tff(c_28, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_6])).
% 1.66/1.13  tff(c_32, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 1.66/1.13  tff(c_34, plain, (![C_14, B_15, A_16]: (r1_tarski(C_14, k7_relat_1(B_15, A_16)) | ~r1_tarski(C_14, B_15) | ~r1_tarski(k1_relat_1(C_14), A_16) | ~v1_relat_1(C_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.13  tff(c_36, plain, (![B_15]: (r1_tarski('#skF_3', k7_relat_1(B_15, '#skF_1')) | ~r1_tarski('#skF_3', B_15) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_32, c_34])).
% 1.66/1.13  tff(c_43, plain, (![B_17]: (r1_tarski('#skF_3', k7_relat_1(B_17, '#skF_1')) | ~r1_tarski('#skF_3', B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 1.66/1.13  tff(c_8, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.13  tff(c_46, plain, (~r1_tarski('#skF_3', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_43, c_8])).
% 1.66/1.13  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_46])).
% 1.66/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  Inference rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Ref     : 0
% 1.66/1.13  #Sup     : 8
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 0
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 5
% 1.66/1.13  #Tautology    : 2
% 1.66/1.13  #SimpNegUnit  : 0
% 1.66/1.13  #BackRed      : 0
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.13  Preprocessing        : 0.26
% 1.66/1.13  Parsing              : 0.15
% 1.66/1.13  CNF conversion       : 0.02
% 1.66/1.13  Main loop            : 0.09
% 1.66/1.13  Inferencing          : 0.05
% 1.66/1.13  Reduction            : 0.02
% 1.66/1.13  Demodulation         : 0.02
% 1.66/1.13  BG Simplification    : 0.01
% 1.66/1.13  Subsumption          : 0.01
% 1.66/1.13  Abstraction          : 0.00
% 1.66/1.13  MUC search           : 0.00
% 1.66/1.13  Cooper               : 0.00
% 1.66/1.13  Total                : 0.38
% 1.66/1.13  Index Insertion      : 0.00
% 1.66/1.13  Index Deletion       : 0.00
% 1.66/1.13  Index Matching       : 0.00
% 1.66/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
