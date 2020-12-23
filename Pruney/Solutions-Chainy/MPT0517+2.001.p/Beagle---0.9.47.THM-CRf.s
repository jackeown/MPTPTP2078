%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  49 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [D_56,E_57,B_58,A_59] :
      ( r2_hidden(k4_tarski(D_56,E_57),B_58)
      | ~ r2_hidden(k4_tarski(D_56,E_57),k8_relat_1(A_59,B_58))
      | ~ v1_relat_1(k8_relat_1(A_59,B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_83,B_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_83,B_84),B_85),'#skF_6'(k8_relat_1(A_83,B_84),B_85)),B_84)
      | ~ v1_relat_1(B_84)
      | r1_tarski(k8_relat_1(A_83,B_84),B_85)
      | ~ v1_relat_1(k8_relat_1(A_83,B_84)) ) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [B_86,A_87] :
      ( ~ v1_relat_1(B_86)
      | r1_tarski(k8_relat_1(A_87,B_86),B_86)
      | ~ v1_relat_1(k8_relat_1(A_87,B_86)) ) ),
    inference(resolution,[status(thm)],[c_121,c_22])).

tff(c_28,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_156,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_150])).

tff(c_159,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.28  
% 1.91/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.15/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.15/1.28  
% 2.15/1.29  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.15/1.29  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.15/1.29  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 2.15/1.29  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 2.15/1.29  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.15/1.29  tff(c_26, plain, (![A_36, B_37]: (v1_relat_1(k8_relat_1(A_36, B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_24, plain, (![A_19, B_29]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), A_19) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_64, plain, (![D_56, E_57, B_58, A_59]: (r2_hidden(k4_tarski(D_56, E_57), B_58) | ~r2_hidden(k4_tarski(D_56, E_57), k8_relat_1(A_59, B_58)) | ~v1_relat_1(k8_relat_1(A_59, B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.29  tff(c_121, plain, (![A_83, B_84, B_85]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_83, B_84), B_85), '#skF_6'(k8_relat_1(A_83, B_84), B_85)), B_84) | ~v1_relat_1(B_84) | r1_tarski(k8_relat_1(A_83, B_84), B_85) | ~v1_relat_1(k8_relat_1(A_83, B_84)))), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.15/1.29  tff(c_22, plain, (![A_19, B_29]: (~r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_29) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_140, plain, (![B_86, A_87]: (~v1_relat_1(B_86) | r1_tarski(k8_relat_1(A_87, B_86), B_86) | ~v1_relat_1(k8_relat_1(A_87, B_86)))), inference(resolution, [status(thm)], [c_121, c_22])).
% 2.15/1.29  tff(c_28, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.15/1.29  tff(c_150, plain, (~v1_relat_1('#skF_8') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_140, c_28])).
% 2.15/1.29  tff(c_156, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_150])).
% 2.15/1.29  tff(c_159, plain, (~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_156])).
% 2.15/1.29  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_159])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 27
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 0
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 3
% 2.15/1.29  #Demod        : 2
% 2.15/1.29  #Tautology    : 4
% 2.15/1.29  #SimpNegUnit  : 0
% 2.15/1.29  #BackRed      : 0
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.29
% 2.15/1.29  Parsing              : 0.15
% 2.15/1.29  CNF conversion       : 0.03
% 2.15/1.29  Main loop            : 0.20
% 2.15/1.29  Inferencing          : 0.08
% 2.15/1.29  Reduction            : 0.04
% 2.15/1.29  Demodulation         : 0.03
% 2.15/1.29  BG Simplification    : 0.02
% 2.15/1.29  Subsumption          : 0.05
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.51
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
