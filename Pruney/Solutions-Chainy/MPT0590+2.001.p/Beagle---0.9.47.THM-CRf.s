%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
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
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_51,C_52] :
      ( r2_hidden(k4_tarski('#skF_5'(A_51,k2_relat_1(A_51),C_52),C_52),A_51)
      | ~ r2_hidden(C_52,k2_relat_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [C_53,D_54,C_55] :
      ( r2_hidden(C_53,D_54)
      | ~ r2_hidden(C_53,k2_relat_1(k2_zfmisc_1(C_55,D_54))) ) ),
    inference(resolution,[status(thm)],[c_51,c_10])).

tff(c_197,plain,(
    ! [C_81,D_82,B_83] :
      ( r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_81,D_82)),B_83),D_82)
      | r1_tarski(k2_relat_1(k2_zfmisc_1(C_81,D_82)),B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_217,plain,(
    ! [C_81,D_82] : r1_tarski(k2_relat_1(k2_zfmisc_1(C_81,D_82)),D_82) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.10/1.28  
% 2.10/1.28  %Foreground sorts:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Background operators:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Foreground operators:
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.10/1.28  
% 2.10/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.29  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.10/1.29  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.10/1.29  tff(f_49, negated_conjecture, ~(![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 2.10/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.29  tff(c_51, plain, (![A_51, C_52]: (r2_hidden(k4_tarski('#skF_5'(A_51, k2_relat_1(A_51), C_52), C_52), A_51) | ~r2_hidden(C_52, k2_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.29  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.29  tff(c_69, plain, (![C_53, D_54, C_55]: (r2_hidden(C_53, D_54) | ~r2_hidden(C_53, k2_relat_1(k2_zfmisc_1(C_55, D_54))))), inference(resolution, [status(thm)], [c_51, c_10])).
% 2.10/1.29  tff(c_197, plain, (![C_81, D_82, B_83]: (r2_hidden('#skF_1'(k2_relat_1(k2_zfmisc_1(C_81, D_82)), B_83), D_82) | r1_tarski(k2_relat_1(k2_zfmisc_1(C_81, D_82)), B_83))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.10/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.29  tff(c_217, plain, (![C_81, D_82]: (r1_tarski(k2_relat_1(k2_zfmisc_1(C_81, D_82)), D_82))), inference(resolution, [status(thm)], [c_197, c_4])).
% 2.10/1.29  tff(c_26, plain, (~r1_tarski(k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.29  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_26])).
% 2.10/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  Inference rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Ref     : 0
% 2.10/1.29  #Sup     : 50
% 2.10/1.29  #Fact    : 0
% 2.10/1.29  #Define  : 0
% 2.10/1.29  #Split   : 0
% 2.10/1.29  #Chain   : 0
% 2.10/1.29  #Close   : 0
% 2.10/1.29  
% 2.10/1.29  Ordering : KBO
% 2.10/1.29  
% 2.10/1.29  Simplification rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Subsume      : 0
% 2.10/1.29  #Demod        : 1
% 2.10/1.29  #Tautology    : 6
% 2.10/1.29  #SimpNegUnit  : 0
% 2.10/1.29  #BackRed      : 1
% 2.10/1.29  
% 2.10/1.29  #Partial instantiations: 0
% 2.10/1.29  #Strategies tried      : 1
% 2.10/1.29  
% 2.10/1.29  Timing (in seconds)
% 2.10/1.29  ----------------------
% 2.10/1.29  Preprocessing        : 0.28
% 2.10/1.29  Parsing              : 0.16
% 2.10/1.29  CNF conversion       : 0.02
% 2.10/1.29  Main loop            : 0.20
% 2.10/1.29  Inferencing          : 0.09
% 2.10/1.29  Reduction            : 0.04
% 2.10/1.29  Demodulation         : 0.03
% 2.10/1.29  BG Simplification    : 0.01
% 2.10/1.29  Subsumption          : 0.05
% 2.10/1.29  Abstraction          : 0.01
% 2.10/1.29  MUC search           : 0.00
% 2.10/1.29  Cooper               : 0.00
% 2.10/1.29  Total                : 0.51
% 2.10/1.29  Index Insertion      : 0.00
% 2.10/1.29  Index Deletion       : 0.00
% 2.10/1.29  Index Matching       : 0.00
% 2.10/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
