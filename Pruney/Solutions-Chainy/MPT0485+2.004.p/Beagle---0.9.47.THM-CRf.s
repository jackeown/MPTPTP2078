%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  45 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_6] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_6)),A_6) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_12),B_13),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,A_6)
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_65,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k2_relat_1(A_20),k2_relat_1(B_21))
      | ~ r1_tarski(A_20,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(A_22,k6_relat_1(k2_relat_1(B_23))) = A_22
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_65,c_12])).

tff(c_14,plain,(
    k5_relat_1('#skF_1',k6_relat_1(k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_111,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_106])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.79/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.16  
% 1.79/1.17  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.79/1.17  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 1.79/1.17  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 1.79/1.17  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.79/1.17  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.79/1.17  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.79/1.17  tff(c_10, plain, (![A_6]: (k5_relat_1(k6_relat_1(k1_relat_1(A_6)), A_6)=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.17  tff(c_31, plain, (![A_12, B_13]: (r1_tarski(k5_relat_1(k6_relat_1(A_12), B_13), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.17  tff(c_34, plain, (![A_6]: (r1_tarski(A_6, A_6) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_31])).
% 1.79/1.17  tff(c_65, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(A_20), k2_relat_1(B_21)) | ~r1_tarski(A_20, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.17  tff(c_12, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.17  tff(c_70, plain, (![A_22, B_23]: (k5_relat_1(A_22, k6_relat_1(k2_relat_1(B_23)))=A_22 | ~r1_tarski(A_22, B_23) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_65, c_12])).
% 1.79/1.17  tff(c_14, plain, (k5_relat_1('#skF_1', k6_relat_1(k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.79/1.17  tff(c_91, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_70, c_14])).
% 1.79/1.17  tff(c_106, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_91])).
% 1.79/1.17  tff(c_111, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_106])).
% 1.79/1.17  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_111])).
% 1.79/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  Inference rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Ref     : 0
% 1.79/1.17  #Sup     : 21
% 1.79/1.17  #Fact    : 0
% 1.79/1.17  #Define  : 0
% 1.79/1.17  #Split   : 0
% 1.79/1.17  #Chain   : 0
% 1.79/1.17  #Close   : 0
% 1.79/1.17  
% 1.79/1.17  Ordering : KBO
% 1.79/1.17  
% 1.79/1.17  Simplification rules
% 1.79/1.17  ----------------------
% 1.79/1.17  #Subsume      : 2
% 1.79/1.17  #Demod        : 3
% 1.79/1.17  #Tautology    : 8
% 1.79/1.17  #SimpNegUnit  : 0
% 1.79/1.17  #BackRed      : 0
% 1.79/1.17  
% 1.79/1.17  #Partial instantiations: 0
% 1.79/1.17  #Strategies tried      : 1
% 1.79/1.17  
% 1.79/1.17  Timing (in seconds)
% 1.79/1.17  ----------------------
% 1.79/1.17  Preprocessing        : 0.27
% 1.79/1.17  Parsing              : 0.15
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.13
% 1.79/1.17  Inferencing          : 0.06
% 1.79/1.17  Reduction            : 0.03
% 1.79/1.17  Demodulation         : 0.02
% 1.79/1.17  BG Simplification    : 0.01
% 1.79/1.17  Subsumption          : 0.02
% 1.79/1.17  Abstraction          : 0.01
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.43
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
