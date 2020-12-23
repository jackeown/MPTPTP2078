%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  90 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_2'),k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k4_tarski(A_26,'#skF_1'(A_26,B_27,C_28)),C_28)
      | ~ r2_hidden(A_26,k10_relat_1(C_28,B_27))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9] :
      ( k1_funct_1(C_10,A_8) = B_9
      | ~ r2_hidden(k4_tarski(A_8,B_9),C_10)
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [C_32,A_33,B_34] :
      ( k1_funct_1(C_32,A_33) = '#skF_1'(A_33,B_34,C_32)
      | ~ v1_funct_1(C_32)
      | ~ r2_hidden(A_33,k10_relat_1(C_32,B_34))
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_95,plain,(
    ! [A_35,A_36] :
      ( '#skF_1'(A_35,k2_relat_1(A_36),A_36) = k1_funct_1(A_36,A_35)
      | ~ v1_funct_1(A_36)
      | ~ r2_hidden(A_35,k1_relat_1(A_36))
      | ~ v1_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_106,plain,
    ( '#skF_1'('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_funct_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_112,plain,(
    '#skF_1'('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_funct_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_106])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),k2_relat_1(C_3))
      | ~ r2_hidden(A_1,k10_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_119,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_2'),k2_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_128,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_2'),k2_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_2',k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_128])).

tff(c_152,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_129])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.34  
% 1.79/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.34  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 1.79/1.34  
% 1.79/1.34  %Foreground sorts:
% 1.79/1.34  
% 1.79/1.34  
% 1.79/1.34  %Background operators:
% 1.79/1.34  
% 1.79/1.34  
% 1.79/1.34  %Foreground operators:
% 1.79/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.79/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.34  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.34  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.79/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.79/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.34  
% 1.79/1.35  tff(f_59, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.79/1.35  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.79/1.35  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.79/1.35  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.79/1.35  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.35  tff(c_20, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.35  tff(c_10, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.35  tff(c_18, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.35  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.35  tff(c_48, plain, (![A_26, B_27, C_28]: (r2_hidden(k4_tarski(A_26, '#skF_1'(A_26, B_27, C_28)), C_28) | ~r2_hidden(A_26, k10_relat_1(C_28, B_27)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.35  tff(c_14, plain, (![C_10, A_8, B_9]: (k1_funct_1(C_10, A_8)=B_9 | ~r2_hidden(k4_tarski(A_8, B_9), C_10) | ~v1_funct_1(C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.35  tff(c_76, plain, (![C_32, A_33, B_34]: (k1_funct_1(C_32, A_33)='#skF_1'(A_33, B_34, C_32) | ~v1_funct_1(C_32) | ~r2_hidden(A_33, k10_relat_1(C_32, B_34)) | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_48, c_14])).
% 1.79/1.35  tff(c_95, plain, (![A_35, A_36]: ('#skF_1'(A_35, k2_relat_1(A_36), A_36)=k1_funct_1(A_36, A_35) | ~v1_funct_1(A_36) | ~r2_hidden(A_35, k1_relat_1(A_36)) | ~v1_relat_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_10, c_76])).
% 1.79/1.35  tff(c_106, plain, ('#skF_1'('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_funct_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_95])).
% 1.79/1.35  tff(c_112, plain, ('#skF_1'('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_funct_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_106])).
% 1.79/1.35  tff(c_8, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), k2_relat_1(C_3)) | ~r2_hidden(A_1, k10_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.35  tff(c_119, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 1.79/1.35  tff(c_128, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_2'), k2_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_119])).
% 1.79/1.35  tff(c_129, plain, (~r2_hidden('#skF_2', k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_18, c_128])).
% 1.79/1.35  tff(c_152, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_129])).
% 1.79/1.35  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_152])).
% 1.79/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.35  
% 1.79/1.35  Inference rules
% 1.79/1.35  ----------------------
% 1.79/1.35  #Ref     : 0
% 1.79/1.35  #Sup     : 29
% 1.79/1.35  #Fact    : 0
% 1.79/1.35  #Define  : 0
% 1.79/1.35  #Split   : 0
% 1.79/1.35  #Chain   : 0
% 1.79/1.35  #Close   : 0
% 1.79/1.35  
% 1.79/1.35  Ordering : KBO
% 1.79/1.35  
% 1.79/1.35  Simplification rules
% 1.79/1.35  ----------------------
% 1.79/1.35  #Subsume      : 0
% 1.79/1.35  #Demod        : 7
% 1.79/1.35  #Tautology    : 7
% 1.79/1.35  #SimpNegUnit  : 2
% 1.79/1.35  #BackRed      : 0
% 1.79/1.35  
% 1.79/1.35  #Partial instantiations: 0
% 1.79/1.35  #Strategies tried      : 1
% 1.79/1.35  
% 1.79/1.35  Timing (in seconds)
% 1.79/1.35  ----------------------
% 1.79/1.35  Preprocessing        : 0.31
% 1.79/1.35  Parsing              : 0.17
% 1.79/1.35  CNF conversion       : 0.02
% 1.79/1.35  Main loop            : 0.16
% 1.79/1.35  Inferencing          : 0.07
% 1.79/1.35  Reduction            : 0.04
% 1.79/1.35  Demodulation         : 0.03
% 1.79/1.35  BG Simplification    : 0.01
% 1.79/1.35  Subsumption          : 0.03
% 1.79/1.35  Abstraction          : 0.01
% 1.79/1.35  MUC search           : 0.00
% 1.79/1.35  Cooper               : 0.00
% 1.79/1.35  Total                : 0.49
% 1.79/1.35  Index Insertion      : 0.00
% 1.79/1.35  Index Deletion       : 0.00
% 1.79/1.35  Index Matching       : 0.00
% 1.79/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
