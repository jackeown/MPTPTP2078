%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 144 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( ( r1_tarski(k1_relat_1(C),A)
              & r1_tarski(C,B) )
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31,plain,(
    r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_16])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [A_23,B_24,B_25] :
      ( r2_hidden('#skF_1'(A_23,B_24),B_25)
      | ~ r1_tarski(A_23,B_25)
      | r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_26,B_27,B_28,B_29] :
      ( r2_hidden('#skF_1'(A_26,B_27),B_28)
      | ~ r1_tarski(B_29,B_28)
      | ~ r1_tarski(A_26,B_29)
      | r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_71,plain,(
    ! [A_33,B_34,B_35,A_36] :
      ( r2_hidden('#skF_1'(A_33,B_34),B_35)
      | ~ r1_tarski(A_33,k7_relat_1(B_35,A_36))
      | r1_tarski(A_33,B_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_75,plain,(
    ! [B_34] :
      ( r2_hidden('#skF_1'('#skF_2',B_34),'#skF_3')
      | r1_tarski('#skF_2',B_34)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_31,c_71])).

tff(c_99,plain,(
    ! [B_40] :
      ( r2_hidden('#skF_1'('#skF_2',B_40),'#skF_3')
      | r1_tarski('#skF_2',B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_105])).

tff(c_111,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_25,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_1'(A_17,B_18),A_17)
      | r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_17] : r1_tarski(A_17,A_17) ),
    inference(resolution,[status(thm)],[c_25,c_4])).

tff(c_148,plain,(
    ! [C_54,B_55,A_56] :
      ( r1_tarski(C_54,k7_relat_1(B_55,A_56))
      | ~ r1_tarski(C_54,B_55)
      | ~ r1_tarski(k1_relat_1(C_54),A_56)
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [C_59,B_60] :
      ( r1_tarski(C_59,k7_relat_1(B_60,k1_relat_1(C_59)))
      | ~ r1_tarski(C_59,B_60)
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_30,c_148])).

tff(c_115,plain,(
    ~ r1_tarski('#skF_2',k7_relat_1('#skF_3',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_16])).

tff(c_179,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_115])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_111,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  
% 1.96/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.18  
% 1.96/1.18  %Foreground sorts:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Background operators:
% 1.96/1.18  
% 1.96/1.18  
% 1.96/1.18  %Foreground operators:
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.18  
% 1.96/1.19  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 1.96/1.19  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.96/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.96/1.19  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 1.96/1.19  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.19  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.19  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.19  tff(c_31, plain, (r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_22])).
% 1.96/1.19  tff(c_16, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.19  tff(c_38, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_16])).
% 1.96/1.19  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.19  tff(c_33, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.19  tff(c_39, plain, (![A_23, B_24, B_25]: (r2_hidden('#skF_1'(A_23, B_24), B_25) | ~r1_tarski(A_23, B_25) | r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_6, c_33])).
% 1.96/1.19  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.19  tff(c_48, plain, (![A_26, B_27, B_28, B_29]: (r2_hidden('#skF_1'(A_26, B_27), B_28) | ~r1_tarski(B_29, B_28) | ~r1_tarski(A_26, B_29) | r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_39, c_2])).
% 1.96/1.19  tff(c_71, plain, (![A_33, B_34, B_35, A_36]: (r2_hidden('#skF_1'(A_33, B_34), B_35) | ~r1_tarski(A_33, k7_relat_1(B_35, A_36)) | r1_tarski(A_33, B_34) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_10, c_48])).
% 1.96/1.19  tff(c_75, plain, (![B_34]: (r2_hidden('#skF_1'('#skF_2', B_34), '#skF_3') | r1_tarski('#skF_2', B_34) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_31, c_71])).
% 1.96/1.19  tff(c_99, plain, (![B_40]: (r2_hidden('#skF_1'('#skF_2', B_40), '#skF_3') | r1_tarski('#skF_2', B_40))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_75])).
% 1.96/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.19  tff(c_105, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_99, c_4])).
% 1.96/1.19  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_105])).
% 1.96/1.19  tff(c_111, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 1.96/1.19  tff(c_25, plain, (![A_17, B_18]: (r2_hidden('#skF_1'(A_17, B_18), A_17) | r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.19  tff(c_30, plain, (![A_17]: (r1_tarski(A_17, A_17))), inference(resolution, [status(thm)], [c_25, c_4])).
% 1.96/1.19  tff(c_148, plain, (![C_54, B_55, A_56]: (r1_tarski(C_54, k7_relat_1(B_55, A_56)) | ~r1_tarski(C_54, B_55) | ~r1_tarski(k1_relat_1(C_54), A_56) | ~v1_relat_1(C_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_171, plain, (![C_59, B_60]: (r1_tarski(C_59, k7_relat_1(B_60, k1_relat_1(C_59))) | ~r1_tarski(C_59, B_60) | ~v1_relat_1(C_59) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_30, c_148])).
% 1.96/1.19  tff(c_115, plain, (~r1_tarski('#skF_2', k7_relat_1('#skF_3', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_16])).
% 1.96/1.19  tff(c_179, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_171, c_115])).
% 1.96/1.19  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_111, c_179])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 33
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 1
% 1.96/1.19  #Chain   : 0
% 1.96/1.19  #Close   : 0
% 1.96/1.19  
% 1.96/1.19  Ordering : KBO
% 1.96/1.19  
% 1.96/1.19  Simplification rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Subsume      : 3
% 1.96/1.19  #Demod        : 9
% 1.96/1.19  #Tautology    : 5
% 1.96/1.19  #SimpNegUnit  : 1
% 1.96/1.19  #BackRed      : 0
% 1.96/1.19  
% 1.96/1.19  #Partial instantiations: 0
% 1.96/1.19  #Strategies tried      : 1
% 1.96/1.19  
% 1.96/1.20  Timing (in seconds)
% 1.96/1.20  ----------------------
% 2.02/1.20  Preprocessing        : 0.25
% 2.02/1.20  Parsing              : 0.14
% 2.02/1.20  CNF conversion       : 0.02
% 2.02/1.20  Main loop            : 0.19
% 2.02/1.20  Inferencing          : 0.07
% 2.02/1.20  Reduction            : 0.05
% 2.02/1.20  Demodulation         : 0.03
% 2.02/1.20  BG Simplification    : 0.01
% 2.02/1.20  Subsumption          : 0.04
% 2.02/1.20  Abstraction          : 0.01
% 2.02/1.20  MUC search           : 0.00
% 2.02/1.20  Cooper               : 0.00
% 2.02/1.20  Total                : 0.47
% 2.02/1.20  Index Insertion      : 0.00
% 2.02/1.20  Index Deletion       : 0.00
% 2.02/1.20  Index Matching       : 0.00
% 2.02/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
