%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  80 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_30,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_51,B_52] :
      ( k4_tarski(k1_mcart_1(A_51),k2_mcart_1(A_51)) = A_51
      | ~ r2_hidden(A_51,B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_73,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_69])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_54] :
      ( r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1(A_54))
      | ~ r2_hidden('#skF_10',A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_36,plain,(
    ! [A_48,B_49] :
      ( k4_tarski(k1_mcart_1(A_48),k2_mcart_1(A_48)) = A_48
      | ~ r2_hidden(A_48,B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_41,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_50] :
      ( r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1(A_50))
      | ~ r2_hidden('#skF_10',A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_4])).

tff(c_28,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1('#skF_9'))
    | ~ r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_10'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_57,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_35])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_63,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_63])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.17  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.81/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.81/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.17  tff('#skF_10', type, '#skF_10': $i).
% 1.81/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.17  tff('#skF_9', type, '#skF_9': $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.81/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.81/1.17  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 1.81/1.17  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.81/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.17  
% 1.81/1.18  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 1.81/1.18  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.81/1.18  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.81/1.18  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.81/1.18  tff(c_30, plain, (r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.18  tff(c_32, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.18  tff(c_65, plain, (![A_51, B_52]: (k4_tarski(k1_mcart_1(A_51), k2_mcart_1(A_51))=A_51 | ~r2_hidden(A_51, B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.18  tff(c_69, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_65])).
% 1.81/1.18  tff(c_73, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_69])).
% 1.81/1.18  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.18  tff(c_88, plain, (![A_54]: (r2_hidden(k2_mcart_1('#skF_10'), k2_relat_1(A_54)) | ~r2_hidden('#skF_10', A_54))), inference(superposition, [status(thm), theory('equality')], [c_73, c_16])).
% 1.81/1.18  tff(c_36, plain, (![A_48, B_49]: (k4_tarski(k1_mcart_1(A_48), k2_mcart_1(A_48))=A_48 | ~r2_hidden(A_48, B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.18  tff(c_38, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_36])).
% 1.81/1.18  tff(c_41, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 1.81/1.18  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.18  tff(c_52, plain, (![A_50]: (r2_hidden(k1_mcart_1('#skF_10'), k1_relat_1(A_50)) | ~r2_hidden('#skF_10', A_50))), inference(superposition, [status(thm), theory('equality')], [c_41, c_4])).
% 1.81/1.18  tff(c_28, plain, (~r2_hidden(k2_mcart_1('#skF_10'), k2_relat_1('#skF_9')) | ~r2_hidden(k1_mcart_1('#skF_10'), k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.18  tff(c_35, plain, (~r2_hidden(k1_mcart_1('#skF_10'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_28])).
% 1.81/1.18  tff(c_57, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_52, c_35])).
% 1.81/1.18  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 1.81/1.18  tff(c_63, plain, (~r2_hidden(k2_mcart_1('#skF_10'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_28])).
% 1.81/1.18  tff(c_93, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_88, c_63])).
% 1.81/1.18  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_93])).
% 1.81/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  Inference rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Ref     : 0
% 1.81/1.18  #Sup     : 16
% 1.81/1.18  #Fact    : 0
% 1.81/1.18  #Define  : 0
% 1.81/1.18  #Split   : 1
% 1.81/1.18  #Chain   : 0
% 1.81/1.18  #Close   : 0
% 1.81/1.18  
% 1.81/1.18  Ordering : KBO
% 1.81/1.18  
% 1.81/1.18  Simplification rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Subsume      : 0
% 1.81/1.18  #Demod        : 4
% 1.81/1.18  #Tautology    : 4
% 1.81/1.18  #SimpNegUnit  : 0
% 1.81/1.18  #BackRed      : 0
% 1.81/1.18  
% 1.81/1.18  #Partial instantiations: 0
% 1.81/1.18  #Strategies tried      : 1
% 1.81/1.18  
% 1.81/1.18  Timing (in seconds)
% 1.81/1.18  ----------------------
% 1.81/1.18  Preprocessing        : 0.26
% 1.81/1.18  Parsing              : 0.14
% 1.81/1.18  CNF conversion       : 0.02
% 1.81/1.18  Main loop            : 0.11
% 1.81/1.18  Inferencing          : 0.04
% 1.81/1.18  Reduction            : 0.03
% 1.81/1.18  Demodulation         : 0.02
% 1.81/1.18  BG Simplification    : 0.01
% 1.81/1.18  Subsumption          : 0.02
% 1.81/1.18  Abstraction          : 0.00
% 1.81/1.18  MUC search           : 0.00
% 1.81/1.18  Cooper               : 0.00
% 1.81/1.18  Total                : 0.40
% 1.81/1.18  Index Insertion      : 0.00
% 1.81/1.18  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
