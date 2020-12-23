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
% DateTime   : Thu Dec  3 10:00:33 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  95 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,(
    ! [A_14] : r1_tarski(A_14,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_4])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden('#skF_2'(A_26,B_27,C_28),k1_relat_1(C_28))
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_26,B_27,C_28,B_2] :
      ( r2_hidden('#skF_2'(A_26,B_27,C_28),B_2)
      | ~ r1_tarski(k1_relat_1(C_28),B_2)
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_7,C_8),A_6),C_8)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),k1_relat_1(C_8))
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_48,C_49,B_50,D_51] :
      ( r2_hidden(A_48,k9_relat_1(C_49,B_50))
      | ~ r2_hidden(D_51,B_50)
      | ~ r2_hidden(k4_tarski(D_51,A_48),C_49)
      | ~ r2_hidden(D_51,k1_relat_1(C_49))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [B_98,A_96,A_99,C_97,C_100] :
      ( r2_hidden(A_96,k9_relat_1(C_100,k1_relat_1(C_97)))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_99,B_98,C_97),A_96),C_100)
      | ~ r2_hidden('#skF_2'(A_99,B_98,C_97),k1_relat_1(C_100))
      | ~ v1_relat_1(C_100)
      | ~ r2_hidden(A_99,k9_relat_1(C_97,B_98))
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_187,plain,(
    ! [A_101,C_102,B_103] :
      ( r2_hidden(A_101,k9_relat_1(C_102,k1_relat_1(C_102)))
      | ~ r2_hidden('#skF_2'(A_101,B_103,C_102),k1_relat_1(C_102))
      | ~ r2_hidden(A_101,k9_relat_1(C_102,B_103))
      | ~ v1_relat_1(C_102) ) ),
    inference(resolution,[status(thm)],[c_12,c_178])).

tff(c_191,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(A_26,k9_relat_1(C_28,k1_relat_1(C_28)))
      | ~ r1_tarski(k1_relat_1(C_28),k1_relat_1(C_28))
      | ~ r2_hidden(A_26,k9_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(resolution,[status(thm)],[c_47,c_187])).

tff(c_209,plain,(
    ! [A_104,C_105,B_106] :
      ( r2_hidden(A_104,k9_relat_1(C_105,k1_relat_1(C_105)))
      | ~ r2_hidden(A_104,k9_relat_1(C_105,B_106))
      | ~ v1_relat_1(C_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_191])).

tff(c_238,plain,(
    ! [C_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_107,B_108),B_109),k9_relat_1(C_107,k1_relat_1(C_107)))
      | ~ v1_relat_1(C_107)
      | r1_tarski(k9_relat_1(C_107,B_108),B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_258,plain,(
    ! [C_110,B_111] :
      ( ~ v1_relat_1(C_110)
      | r1_tarski(k9_relat_1(C_110,B_111),k9_relat_1(C_110,k1_relat_1(C_110))) ) ),
    inference(resolution,[status(thm)],[c_238,c_4])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k9_relat_1('#skF_4',k1_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_271,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_16])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.29/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.29/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.30  
% 2.29/1.31  tff(f_48, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.29/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.31  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.29/1.31  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_20, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_25, plain, (![A_14]: (r1_tarski(A_14, A_14))), inference(resolution, [status(thm)], [c_20, c_4])).
% 2.29/1.31  tff(c_44, plain, (![A_26, B_27, C_28]: (r2_hidden('#skF_2'(A_26, B_27, C_28), k1_relat_1(C_28)) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_47, plain, (![A_26, B_27, C_28, B_2]: (r2_hidden('#skF_2'(A_26, B_27, C_28), B_2) | ~r1_tarski(k1_relat_1(C_28), B_2) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.29/1.31  tff(c_12, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_7, C_8), A_6), C_8) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.31  tff(c_14, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), k1_relat_1(C_8)) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.31  tff(c_68, plain, (![A_48, C_49, B_50, D_51]: (r2_hidden(A_48, k9_relat_1(C_49, B_50)) | ~r2_hidden(D_51, B_50) | ~r2_hidden(k4_tarski(D_51, A_48), C_49) | ~r2_hidden(D_51, k1_relat_1(C_49)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.31  tff(c_178, plain, (![B_98, A_96, A_99, C_97, C_100]: (r2_hidden(A_96, k9_relat_1(C_100, k1_relat_1(C_97))) | ~r2_hidden(k4_tarski('#skF_2'(A_99, B_98, C_97), A_96), C_100) | ~r2_hidden('#skF_2'(A_99, B_98, C_97), k1_relat_1(C_100)) | ~v1_relat_1(C_100) | ~r2_hidden(A_99, k9_relat_1(C_97, B_98)) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_14, c_68])).
% 2.29/1.31  tff(c_187, plain, (![A_101, C_102, B_103]: (r2_hidden(A_101, k9_relat_1(C_102, k1_relat_1(C_102))) | ~r2_hidden('#skF_2'(A_101, B_103, C_102), k1_relat_1(C_102)) | ~r2_hidden(A_101, k9_relat_1(C_102, B_103)) | ~v1_relat_1(C_102))), inference(resolution, [status(thm)], [c_12, c_178])).
% 2.29/1.31  tff(c_191, plain, (![A_26, C_28, B_27]: (r2_hidden(A_26, k9_relat_1(C_28, k1_relat_1(C_28))) | ~r1_tarski(k1_relat_1(C_28), k1_relat_1(C_28)) | ~r2_hidden(A_26, k9_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(resolution, [status(thm)], [c_47, c_187])).
% 2.29/1.31  tff(c_209, plain, (![A_104, C_105, B_106]: (r2_hidden(A_104, k9_relat_1(C_105, k1_relat_1(C_105))) | ~r2_hidden(A_104, k9_relat_1(C_105, B_106)) | ~v1_relat_1(C_105))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_191])).
% 2.29/1.31  tff(c_238, plain, (![C_107, B_108, B_109]: (r2_hidden('#skF_1'(k9_relat_1(C_107, B_108), B_109), k9_relat_1(C_107, k1_relat_1(C_107))) | ~v1_relat_1(C_107) | r1_tarski(k9_relat_1(C_107, B_108), B_109))), inference(resolution, [status(thm)], [c_6, c_209])).
% 2.29/1.31  tff(c_258, plain, (![C_110, B_111]: (~v1_relat_1(C_110) | r1_tarski(k9_relat_1(C_110, B_111), k9_relat_1(C_110, k1_relat_1(C_110))))), inference(resolution, [status(thm)], [c_238, c_4])).
% 2.29/1.31  tff(c_16, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k9_relat_1('#skF_4', k1_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.31  tff(c_271, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_258, c_16])).
% 2.29/1.31  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_271])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 61
% 2.29/1.31  #Fact    : 0
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 0
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 8
% 2.29/1.31  #Demod        : 5
% 2.29/1.31  #Tautology    : 6
% 2.29/1.31  #SimpNegUnit  : 0
% 2.29/1.31  #BackRed      : 0
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.26
% 2.29/1.31  Parsing              : 0.14
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.28
% 2.29/1.31  Inferencing          : 0.13
% 2.29/1.31  Reduction            : 0.06
% 2.29/1.31  Demodulation         : 0.04
% 2.29/1.31  BG Simplification    : 0.01
% 2.29/1.31  Subsumption          : 0.07
% 2.29/1.31  Abstraction          : 0.01
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.57
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.31  Index Deletion       : 0.00
% 2.29/1.31  Index Matching       : 0.00
% 2.29/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
