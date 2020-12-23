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
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

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
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.27  % Computer   : n016.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 18:06:19 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.10  
% 1.83/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.11  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.83/1.11  
% 1.83/1.11  %Foreground sorts:
% 1.83/1.11  
% 1.83/1.11  
% 1.83/1.11  %Background operators:
% 1.83/1.11  
% 1.83/1.11  
% 1.83/1.11  %Foreground operators:
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.11  tff('#skF_7', type, '#skF_7': $i).
% 1.83/1.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.11  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.83/1.11  
% 1.83/1.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.83/1.11  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.83/1.11  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 1.83/1.11  tff(f_49, negated_conjecture, ~(![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 1.83/1.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.11  tff(c_51, plain, (![C_51, A_52]: (r2_hidden(k4_tarski(C_51, '#skF_5'(A_52, k1_relat_1(A_52), C_51)), A_52) | ~r2_hidden(C_51, k1_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.83/1.11  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.11  tff(c_69, plain, (![C_53, C_54, D_55]: (r2_hidden(C_53, C_54) | ~r2_hidden(C_53, k1_relat_1(k2_zfmisc_1(C_54, D_55))))), inference(resolution, [status(thm)], [c_51, c_12])).
% 1.83/1.11  tff(c_197, plain, (![C_81, D_82, B_83]: (r2_hidden('#skF_1'(k1_relat_1(k2_zfmisc_1(C_81, D_82)), B_83), C_81) | r1_tarski(k1_relat_1(k2_zfmisc_1(C_81, D_82)), B_83))), inference(resolution, [status(thm)], [c_6, c_69])).
% 1.83/1.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.11  tff(c_217, plain, (![C_81, D_82]: (r1_tarski(k1_relat_1(k2_zfmisc_1(C_81, D_82)), C_81))), inference(resolution, [status(thm)], [c_197, c_4])).
% 1.83/1.11  tff(c_26, plain, (~r1_tarski(k1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.11  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_26])).
% 1.83/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.11  
% 1.83/1.11  Inference rules
% 1.83/1.11  ----------------------
% 1.83/1.11  #Ref     : 0
% 1.83/1.11  #Sup     : 50
% 1.83/1.11  #Fact    : 0
% 1.83/1.11  #Define  : 0
% 1.83/1.11  #Split   : 0
% 1.83/1.11  #Chain   : 0
% 1.83/1.11  #Close   : 0
% 1.83/1.11  
% 1.83/1.11  Ordering : KBO
% 1.83/1.11  
% 1.83/1.11  Simplification rules
% 1.83/1.11  ----------------------
% 1.83/1.11  #Subsume      : 0
% 1.83/1.11  #Demod        : 1
% 1.83/1.11  #Tautology    : 6
% 1.83/1.11  #SimpNegUnit  : 0
% 1.83/1.11  #BackRed      : 1
% 1.83/1.11  
% 1.83/1.11  #Partial instantiations: 0
% 1.83/1.11  #Strategies tried      : 1
% 1.83/1.11  
% 1.83/1.11  Timing (in seconds)
% 1.83/1.11  ----------------------
% 1.83/1.12  Preprocessing        : 0.28
% 1.83/1.12  Parsing              : 0.15
% 1.83/1.12  CNF conversion       : 0.02
% 1.83/1.12  Main loop            : 0.20
% 1.83/1.12  Inferencing          : 0.09
% 1.83/1.12  Reduction            : 0.04
% 1.83/1.12  Demodulation         : 0.03
% 1.83/1.12  BG Simplification    : 0.01
% 1.83/1.12  Subsumption          : 0.05
% 1.83/1.12  Abstraction          : 0.01
% 1.83/1.12  MUC search           : 0.00
% 1.83/1.12  Cooper               : 0.00
% 1.83/1.12  Total                : 0.50
% 1.83/1.12  Index Insertion      : 0.00
% 1.83/1.12  Index Deletion       : 0.00
% 1.83/1.12  Index Matching       : 0.00
% 1.83/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
