%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  92 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ( r2_hidden(C,A)
             => r2_hidden(k4_tarski(C,C),B) )
         => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski(k6_relat_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(k4_tarski('#skF_5'(A_41,B_42),'#skF_6'(A_41,B_42)),A_41)
      | r1_tarski(A_41,B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18])).

tff(c_62,plain,(
    ! [A_1,B_42] :
      ( r2_hidden('#skF_5'(k6_relat_1(A_1),B_42),A_1)
      | r1_tarski(k6_relat_1(A_1),B_42)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_54,c_34])).

tff(c_70,plain,(
    ! [A_1,B_42] :
      ( r2_hidden('#skF_5'(k6_relat_1(A_1),B_42),A_1)
      | r1_tarski(k6_relat_1(A_1),B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_30,plain,(
    ! [C_28] :
      ( r2_hidden(k4_tarski(C_28,C_28),'#skF_8')
      | ~ r2_hidden(C_28,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_66,plain,(
    ! [A_1,B_42] :
      ( '#skF_6'(k6_relat_1(A_1),B_42) = '#skF_5'(k6_relat_1(A_1),B_42)
      | r1_tarski(k6_relat_1(A_1),B_42)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_54,c_36])).

tff(c_106,plain,(
    ! [A_54,B_55] :
      ( '#skF_6'(k6_relat_1(A_54),B_55) = '#skF_5'(k6_relat_1(A_54),B_55)
      | r1_tarski(k6_relat_1(A_54),B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_110,plain,(
    '#skF_6'(k6_relat_1('#skF_7'),'#skF_8') = '#skF_5'(k6_relat_1('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_106,c_28])).

tff(c_22,plain,(
    ! [A_9,B_19] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_9,B_19),'#skF_6'(A_9,B_19)),B_19)
      | r1_tarski(A_9,B_19)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),'#skF_8'),'#skF_5'(k6_relat_1('#skF_7'),'#skF_8')),'#skF_8')
    | r1_tarski(k6_relat_1('#skF_7'),'#skF_8')
    | ~ v1_relat_1(k6_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_22])).

tff(c_142,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),'#skF_8'),'#skF_5'(k6_relat_1('#skF_7'),'#skF_8')),'#skF_8')
    | r1_tarski(k6_relat_1('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_135])).

tff(c_143,plain,(
    ~ r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'),'#skF_8'),'#skF_5'(k6_relat_1('#skF_7'),'#skF_8')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_142])).

tff(c_152,plain,(
    ~ r2_hidden('#skF_5'(k6_relat_1('#skF_7'),'#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_155,plain,(
    r1_tarski(k6_relat_1('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_152])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.18  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.18  tff('#skF_8', type, '#skF_8': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.84/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.84/1.18  
% 1.84/1.19  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 1.84/1.19  tff(f_48, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.84/1.19  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 1.84/1.19  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_relat_1)).
% 1.84/1.19  tff(c_28, plain, (~r1_tarski(k6_relat_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.19  tff(c_26, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.19  tff(c_54, plain, (![A_41, B_42]: (r2_hidden(k4_tarski('#skF_5'(A_41, B_42), '#skF_6'(A_41, B_42)), A_41) | r1_tarski(A_41, B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.19  tff(c_18, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.19  tff(c_34, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18])).
% 1.84/1.19  tff(c_62, plain, (![A_1, B_42]: (r2_hidden('#skF_5'(k6_relat_1(A_1), B_42), A_1) | r1_tarski(k6_relat_1(A_1), B_42) | ~v1_relat_1(k6_relat_1(A_1)))), inference(resolution, [status(thm)], [c_54, c_34])).
% 1.84/1.19  tff(c_70, plain, (![A_1, B_42]: (r2_hidden('#skF_5'(k6_relat_1(A_1), B_42), A_1) | r1_tarski(k6_relat_1(A_1), B_42))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 1.84/1.19  tff(c_30, plain, (![C_28]: (r2_hidden(k4_tarski(C_28, C_28), '#skF_8') | ~r2_hidden(C_28, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.19  tff(c_16, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.84/1.19  tff(c_36, plain, (![D_8, C_7, A_1]: (D_8=C_7 | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 1.84/1.19  tff(c_66, plain, (![A_1, B_42]: ('#skF_6'(k6_relat_1(A_1), B_42)='#skF_5'(k6_relat_1(A_1), B_42) | r1_tarski(k6_relat_1(A_1), B_42) | ~v1_relat_1(k6_relat_1(A_1)))), inference(resolution, [status(thm)], [c_54, c_36])).
% 1.84/1.19  tff(c_106, plain, (![A_54, B_55]: ('#skF_6'(k6_relat_1(A_54), B_55)='#skF_5'(k6_relat_1(A_54), B_55) | r1_tarski(k6_relat_1(A_54), B_55))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 1.84/1.19  tff(c_110, plain, ('#skF_6'(k6_relat_1('#skF_7'), '#skF_8')='#skF_5'(k6_relat_1('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_106, c_28])).
% 1.84/1.19  tff(c_22, plain, (![A_9, B_19]: (~r2_hidden(k4_tarski('#skF_5'(A_9, B_19), '#skF_6'(A_9, B_19)), B_19) | r1_tarski(A_9, B_19) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.19  tff(c_135, plain, (~r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'), '#skF_8'), '#skF_5'(k6_relat_1('#skF_7'), '#skF_8')), '#skF_8') | r1_tarski(k6_relat_1('#skF_7'), '#skF_8') | ~v1_relat_1(k6_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_22])).
% 1.84/1.19  tff(c_142, plain, (~r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'), '#skF_8'), '#skF_5'(k6_relat_1('#skF_7'), '#skF_8')), '#skF_8') | r1_tarski(k6_relat_1('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_135])).
% 1.84/1.19  tff(c_143, plain, (~r2_hidden(k4_tarski('#skF_5'(k6_relat_1('#skF_7'), '#skF_8'), '#skF_5'(k6_relat_1('#skF_7'), '#skF_8')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_28, c_142])).
% 1.84/1.19  tff(c_152, plain, (~r2_hidden('#skF_5'(k6_relat_1('#skF_7'), '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_143])).
% 1.84/1.19  tff(c_155, plain, (r1_tarski(k6_relat_1('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_70, c_152])).
% 1.84/1.19  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_155])).
% 1.84/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  Inference rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Ref     : 0
% 1.84/1.19  #Sup     : 22
% 1.84/1.19  #Fact    : 0
% 1.84/1.19  #Define  : 0
% 1.84/1.19  #Split   : 0
% 1.84/1.19  #Chain   : 0
% 1.84/1.19  #Close   : 0
% 1.84/1.19  
% 1.84/1.19  Ordering : KBO
% 1.84/1.19  
% 1.84/1.19  Simplification rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Subsume      : 0
% 1.84/1.19  #Demod        : 11
% 1.84/1.19  #Tautology    : 5
% 1.84/1.19  #SimpNegUnit  : 3
% 1.84/1.19  #BackRed      : 0
% 1.84/1.19  
% 1.84/1.19  #Partial instantiations: 0
% 1.84/1.19  #Strategies tried      : 1
% 1.84/1.19  
% 1.84/1.19  Timing (in seconds)
% 1.84/1.19  ----------------------
% 1.84/1.20  Preprocessing        : 0.29
% 1.84/1.20  Parsing              : 0.15
% 1.84/1.20  CNF conversion       : 0.02
% 1.84/1.20  Main loop            : 0.13
% 1.84/1.20  Inferencing          : 0.05
% 1.84/1.20  Reduction            : 0.04
% 1.84/1.20  Demodulation         : 0.03
% 1.84/1.20  BG Simplification    : 0.02
% 1.84/1.20  Subsumption          : 0.02
% 1.84/1.20  Abstraction          : 0.01
% 1.84/1.20  MUC search           : 0.00
% 1.84/1.20  Cooper               : 0.00
% 1.84/1.20  Total                : 0.45
% 1.84/1.20  Index Insertion      : 0.00
% 1.84/1.20  Index Deletion       : 0.00
% 1.84/1.20  Index Matching       : 0.00
% 1.84/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
