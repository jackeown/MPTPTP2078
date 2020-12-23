%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  39 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(k4_tarski(D_130,'#skF_5'(A_131,B_132,k10_relat_1(A_131,B_132),D_130)),A_131)
      | ~ r2_hidden(D_130,k10_relat_1(A_131,B_132))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [C_63,A_48,D_66] :
      ( r2_hidden(C_63,k1_relat_1(A_48))
      | ~ r2_hidden(k4_tarski(C_63,D_66),A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_235,plain,(
    ! [D_133,A_134,B_135] :
      ( r2_hidden(D_133,k1_relat_1(A_134))
      | ~ r2_hidden(D_133,k10_relat_1(A_134,B_135))
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_224,c_28])).

tff(c_316,plain,(
    ! [A_136,B_137,B_138] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_136,B_137),B_138),k1_relat_1(A_136))
      | ~ v1_relat_1(A_136)
      | r1_tarski(k10_relat_1(A_136,B_137),B_138) ) ),
    inference(resolution,[status(thm)],[c_6,c_235])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_328,plain,(
    ! [A_139,B_140] :
      ( ~ v1_relat_1(A_139)
      | r1_tarski(k10_relat_1(A_139,B_140),k1_relat_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_316,c_4])).

tff(c_38,plain,(
    ~ r1_tarski(k10_relat_1('#skF_11','#skF_10'),k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_335,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_328,c_38])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.46  
% 2.38/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 2.38/1.46  
% 2.38/1.46  %Foreground sorts:
% 2.38/1.46  
% 2.38/1.46  
% 2.38/1.46  %Background operators:
% 2.38/1.46  
% 2.38/1.46  
% 2.38/1.46  %Foreground operators:
% 2.38/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.38/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.46  tff('#skF_11', type, '#skF_11': $i).
% 2.38/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.38/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.46  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.38/1.46  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.38/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.38/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.38/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.46  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.38/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.46  
% 2.38/1.47  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.38/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.38/1.47  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.38/1.47  tff(f_53, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.38/1.47  tff(c_40, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.47  tff(c_224, plain, (![D_130, A_131, B_132]: (r2_hidden(k4_tarski(D_130, '#skF_5'(A_131, B_132, k10_relat_1(A_131, B_132), D_130)), A_131) | ~r2_hidden(D_130, k10_relat_1(A_131, B_132)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.47  tff(c_28, plain, (![C_63, A_48, D_66]: (r2_hidden(C_63, k1_relat_1(A_48)) | ~r2_hidden(k4_tarski(C_63, D_66), A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.38/1.47  tff(c_235, plain, (![D_133, A_134, B_135]: (r2_hidden(D_133, k1_relat_1(A_134)) | ~r2_hidden(D_133, k10_relat_1(A_134, B_135)) | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_224, c_28])).
% 2.38/1.47  tff(c_316, plain, (![A_136, B_137, B_138]: (r2_hidden('#skF_1'(k10_relat_1(A_136, B_137), B_138), k1_relat_1(A_136)) | ~v1_relat_1(A_136) | r1_tarski(k10_relat_1(A_136, B_137), B_138))), inference(resolution, [status(thm)], [c_6, c_235])).
% 2.38/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.70/1.47  tff(c_328, plain, (![A_139, B_140]: (~v1_relat_1(A_139) | r1_tarski(k10_relat_1(A_139, B_140), k1_relat_1(A_139)))), inference(resolution, [status(thm)], [c_316, c_4])).
% 2.70/1.47  tff(c_38, plain, (~r1_tarski(k10_relat_1('#skF_11', '#skF_10'), k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.70/1.47  tff(c_335, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_328, c_38])).
% 2.70/1.47  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_335])).
% 2.70/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.47  
% 2.70/1.47  Inference rules
% 2.70/1.47  ----------------------
% 2.70/1.47  #Ref     : 0
% 2.70/1.47  #Sup     : 72
% 2.70/1.47  #Fact    : 0
% 2.70/1.47  #Define  : 0
% 2.70/1.47  #Split   : 0
% 2.70/1.47  #Chain   : 0
% 2.70/1.47  #Close   : 0
% 2.70/1.47  
% 2.70/1.47  Ordering : KBO
% 2.70/1.47  
% 2.70/1.47  Simplification rules
% 2.70/1.47  ----------------------
% 2.70/1.47  #Subsume      : 2
% 2.70/1.47  #Demod        : 1
% 2.70/1.47  #Tautology    : 6
% 2.70/1.47  #SimpNegUnit  : 0
% 2.70/1.47  #BackRed      : 0
% 2.70/1.47  
% 2.70/1.47  #Partial instantiations: 0
% 2.70/1.47  #Strategies tried      : 1
% 2.70/1.47  
% 2.70/1.47  Timing (in seconds)
% 2.70/1.47  ----------------------
% 2.70/1.47  Preprocessing        : 0.38
% 2.70/1.47  Parsing              : 0.19
% 2.70/1.47  CNF conversion       : 0.04
% 2.70/1.47  Main loop            : 0.26
% 2.70/1.47  Inferencing          : 0.10
% 2.70/1.47  Reduction            : 0.06
% 2.70/1.47  Demodulation         : 0.04
% 2.70/1.47  BG Simplification    : 0.03
% 2.70/1.47  Subsumption          : 0.06
% 2.70/1.47  Abstraction          : 0.02
% 2.70/1.47  MUC search           : 0.00
% 2.70/1.47  Cooper               : 0.00
% 2.70/1.47  Total                : 0.67
% 2.70/1.47  Index Insertion      : 0.00
% 2.70/1.47  Index Deletion       : 0.00
% 2.70/1.47  Index Matching       : 0.00
% 2.70/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
