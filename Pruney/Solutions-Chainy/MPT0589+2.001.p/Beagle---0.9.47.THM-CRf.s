%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  28 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [C_51,A_52] :
      ( r2_hidden(k4_tarski(C_51,'#skF_5'(A_52,k1_relat_1(A_52),C_51)),A_52)
      | ~ r2_hidden(C_51,k1_relat_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [C_53,C_54,D_55] :
      ( r2_hidden(C_53,C_54)
      | ~ r2_hidden(C_53,k1_relat_1(k2_zfmisc_1(C_54,D_55))) ) ),
    inference(resolution,[status(thm)],[c_51,c_12])).

tff(c_197,plain,(
    ! [C_81,D_82,B_83] :
      ( r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(C_81,D_82)),B_83),C_81)
      | r1_tarski(k1_relat_1(k2_zfmisc_1(C_81,D_82)),B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_217,plain,(
    ! [C_81,D_82] : r1_tarski(k1_relat_1(k2_zfmisc_1(C_81,D_82)),C_81) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.03/1.26  
% 2.03/1.26  %Foreground sorts:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Background operators:
% 2.03/1.26  
% 2.03/1.26  
% 2.03/1.26  %Foreground operators:
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.03/1.26  
% 2.03/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.27  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.03/1.27  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.03/1.27  tff(f_49, negated_conjecture, ~(![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 2.03/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.27  tff(c_51, plain, (![C_51, A_52]: (r2_hidden(k4_tarski(C_51, '#skF_5'(A_52, k1_relat_1(A_52), C_51)), A_52) | ~r2_hidden(C_51, k1_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.27  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.27  tff(c_69, plain, (![C_53, C_54, D_55]: (r2_hidden(C_53, C_54) | ~r2_hidden(C_53, k1_relat_1(k2_zfmisc_1(C_54, D_55))))), inference(resolution, [status(thm)], [c_51, c_12])).
% 2.03/1.27  tff(c_197, plain, (![C_81, D_82, B_83]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(C_81, D_82)), B_83), C_81) | r1_tarski(k1_relat_1(k2_zfmisc_1(C_81, D_82)), B_83))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.03/1.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.27  tff(c_217, plain, (![C_81, D_82]: (r1_tarski(k1_relat_1(k2_zfmisc_1(C_81, D_82)), C_81))), inference(resolution, [status(thm)], [c_197, c_4])).
% 2.03/1.27  tff(c_26, plain, (~r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.27  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_26])).
% 2.03/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.27  
% 2.03/1.27  Inference rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Ref     : 0
% 2.03/1.27  #Sup     : 50
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 0
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 0
% 2.03/1.27  #Demod        : 1
% 2.03/1.27  #Tautology    : 6
% 2.03/1.27  #SimpNegUnit  : 0
% 2.03/1.27  #BackRed      : 1
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.27  Preprocessing        : 0.27
% 2.03/1.27  Parsing              : 0.14
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.21
% 2.03/1.27  Inferencing          : 0.09
% 2.03/1.27  Reduction            : 0.04
% 2.03/1.27  Demodulation         : 0.03
% 2.03/1.27  BG Simplification    : 0.01
% 2.03/1.27  Subsumption          : 0.05
% 2.03/1.27  Abstraction          : 0.01
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.50
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.27  Index Matching       : 0.00
% 2.03/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
