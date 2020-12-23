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
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,B)
         => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_16] :
      ( k4_tarski('#skF_2'(A_1,B_16),'#skF_3'(A_1,B_16)) = B_16
      | ~ r2_hidden(B_16,A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_30,B_31] :
      ( k4_tarski('#skF_2'(A_30,B_31),'#skF_3'(A_30,B_31)) = B_31
      | ~ r2_hidden(B_31,A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_22,C_23] : k4_tarski(k1_mcart_1(k4_tarski(B_22,C_23)),k2_mcart_1(k4_tarski(B_22,C_23))) = k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [B_37,A_38] :
      ( k4_tarski(k1_mcart_1(B_37),k2_mcart_1(k4_tarski('#skF_2'(A_38,B_37),'#skF_3'(A_38,B_37)))) = k4_tarski('#skF_2'(A_38,B_37),'#skF_3'(A_38,B_37))
      | ~ r2_hidden(B_37,A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_8])).

tff(c_88,plain,(
    ! [B_39,A_40] :
      ( k4_tarski(k1_mcart_1(B_39),k2_mcart_1(B_39)) = k4_tarski('#skF_2'(A_40,B_39),'#skF_3'(A_40,B_39))
      | ~ r2_hidden(B_39,A_40)
      | ~ v1_relat_1(A_40)
      | ~ r2_hidden(B_39,A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_10,plain,(
    k4_tarski(k1_mcart_1('#skF_4'),k2_mcart_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [A_41] :
      ( k4_tarski('#skF_2'(A_41,'#skF_4'),'#skF_3'(A_41,'#skF_4')) != '#skF_4'
      | ~ r2_hidden('#skF_4',A_41)
      | ~ v1_relat_1(A_41)
      | ~ r2_hidden('#skF_4',A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_145,plain,(
    ! [A_42] :
      ( ~ r2_hidden('#skF_4',A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_148,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:02:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 1.66/1.17  
% 1.66/1.17  %Foreground sorts:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Background operators:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Foreground operators:
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.66/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.66/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.66/1.17  
% 1.66/1.18  tff(f_47, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.66/1.18  tff(f_35, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.66/1.18  tff(f_40, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (k4_tarski(k1_mcart_1(A), k2_mcart_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_mcart_1)).
% 1.66/1.18  tff(c_14, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.18  tff(c_12, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.18  tff(c_2, plain, (![A_1, B_16]: (k4_tarski('#skF_2'(A_1, B_16), '#skF_3'(A_1, B_16))=B_16 | ~r2_hidden(B_16, A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.18  tff(c_43, plain, (![A_30, B_31]: (k4_tarski('#skF_2'(A_30, B_31), '#skF_3'(A_30, B_31))=B_31 | ~r2_hidden(B_31, A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.18  tff(c_8, plain, (![B_22, C_23]: (k4_tarski(k1_mcart_1(k4_tarski(B_22, C_23)), k2_mcart_1(k4_tarski(B_22, C_23)))=k4_tarski(B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.18  tff(c_69, plain, (![B_37, A_38]: (k4_tarski(k1_mcart_1(B_37), k2_mcart_1(k4_tarski('#skF_2'(A_38, B_37), '#skF_3'(A_38, B_37))))=k4_tarski('#skF_2'(A_38, B_37), '#skF_3'(A_38, B_37)) | ~r2_hidden(B_37, A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_43, c_8])).
% 1.66/1.18  tff(c_88, plain, (![B_39, A_40]: (k4_tarski(k1_mcart_1(B_39), k2_mcart_1(B_39))=k4_tarski('#skF_2'(A_40, B_39), '#skF_3'(A_40, B_39)) | ~r2_hidden(B_39, A_40) | ~v1_relat_1(A_40) | ~r2_hidden(B_39, A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 1.66/1.18  tff(c_10, plain, (k4_tarski(k1_mcart_1('#skF_4'), k2_mcart_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.18  tff(c_135, plain, (![A_41]: (k4_tarski('#skF_2'(A_41, '#skF_4'), '#skF_3'(A_41, '#skF_4'))!='#skF_4' | ~r2_hidden('#skF_4', A_41) | ~v1_relat_1(A_41) | ~r2_hidden('#skF_4', A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 1.66/1.18  tff(c_145, plain, (![A_42]: (~r2_hidden('#skF_4', A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 1.66/1.18  tff(c_148, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_145])).
% 1.66/1.18  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_148])).
% 1.66/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.18  
% 1.66/1.18  Inference rules
% 1.66/1.18  ----------------------
% 1.66/1.18  #Ref     : 1
% 1.66/1.18  #Sup     : 38
% 1.66/1.18  #Fact    : 0
% 1.66/1.18  #Define  : 0
% 1.66/1.18  #Split   : 0
% 1.66/1.18  #Chain   : 0
% 1.66/1.18  #Close   : 0
% 1.66/1.18  
% 1.66/1.18  Ordering : KBO
% 1.66/1.18  
% 1.66/1.18  Simplification rules
% 1.66/1.18  ----------------------
% 1.66/1.18  #Subsume      : 8
% 1.66/1.18  #Demod        : 5
% 1.66/1.18  #Tautology    : 13
% 1.66/1.18  #SimpNegUnit  : 0
% 1.66/1.18  #BackRed      : 0
% 1.66/1.18  
% 1.66/1.18  #Partial instantiations: 0
% 1.66/1.18  #Strategies tried      : 1
% 1.66/1.18  
% 1.66/1.18  Timing (in seconds)
% 1.66/1.18  ----------------------
% 1.66/1.18  Preprocessing        : 0.26
% 1.66/1.18  Parsing              : 0.14
% 1.66/1.18  CNF conversion       : 0.02
% 1.66/1.18  Main loop            : 0.16
% 1.66/1.18  Inferencing          : 0.08
% 1.66/1.18  Reduction            : 0.04
% 1.66/1.18  Demodulation         : 0.03
% 1.66/1.18  BG Simplification    : 0.01
% 1.66/1.18  Subsumption          : 0.02
% 1.66/1.18  Abstraction          : 0.01
% 1.66/1.18  MUC search           : 0.00
% 1.66/1.18  Cooper               : 0.00
% 1.66/1.18  Total                : 0.44
% 1.66/1.18  Index Insertion      : 0.00
% 1.66/1.18  Index Deletion       : 0.00
% 1.66/1.18  Index Matching       : 0.00
% 1.66/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
