%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:05 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  85 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(k4_tarski('#skF_6'(A_91,B_92,C_93),A_91),C_93)
      | ~ r2_hidden(A_91,k9_relat_1(C_93,B_92))
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_91,B_92,C_93,B_2] :
      ( r2_hidden(k4_tarski('#skF_6'(A_91,B_92,C_93),A_91),B_2)
      | ~ r1_tarski(C_93,B_2)
      | ~ r2_hidden(A_91,k9_relat_1(C_93,B_92))
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_28,plain,(
    ! [A_48,B_49,C_50] :
      ( r2_hidden('#skF_6'(A_48,B_49,C_50),B_49)
      | ~ r2_hidden(A_48,k9_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [D_82,A_83,B_84,E_85] :
      ( r2_hidden(D_82,k9_relat_1(A_83,B_84))
      | ~ r2_hidden(E_85,B_84)
      | ~ r2_hidden(k4_tarski(E_85,D_82),A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_391,plain,(
    ! [B_211,A_214,D_210,C_213,A_212] :
      ( r2_hidden(D_210,k9_relat_1(A_214,B_211))
      | ~ r2_hidden(k4_tarski('#skF_6'(A_212,B_211,C_213),D_210),A_214)
      | ~ v1_relat_1(A_214)
      | ~ r2_hidden(A_212,k9_relat_1(C_213,B_211))
      | ~ v1_relat_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_503,plain,(
    ! [A_218,B_219,B_220,C_221] :
      ( r2_hidden(A_218,k9_relat_1(B_219,B_220))
      | ~ v1_relat_1(B_219)
      | ~ r1_tarski(C_221,B_219)
      | ~ r2_hidden(A_218,k9_relat_1(C_221,B_220))
      | ~ v1_relat_1(C_221) ) ),
    inference(resolution,[status(thm)],[c_144,c_391])).

tff(c_509,plain,(
    ! [A_218,B_220] :
      ( r2_hidden(A_218,k9_relat_1('#skF_9',B_220))
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(A_218,k9_relat_1('#skF_8',B_220))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_503])).

tff(c_517,plain,(
    ! [A_222,B_223] :
      ( r2_hidden(A_222,k9_relat_1('#skF_9',B_223))
      | ~ r2_hidden(A_222,k9_relat_1('#skF_8',B_223)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_509])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_691,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(A_233,k9_relat_1('#skF_9',B_234))
      | ~ r2_hidden('#skF_1'(A_233,k9_relat_1('#skF_9',B_234)),k9_relat_1('#skF_8',B_234)) ) ),
    inference(resolution,[status(thm)],[c_517,c_4])).

tff(c_706,plain,(
    ! [B_234] : r1_tarski(k9_relat_1('#skF_8',B_234),k9_relat_1('#skF_9',B_234)) ),
    inference(resolution,[status(thm)],[c_6,c_691])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_8','#skF_7'),k9_relat_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.64  
% 3.31/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.64  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.31/1.64  
% 3.31/1.64  %Foreground sorts:
% 3.31/1.64  
% 3.31/1.64  
% 3.31/1.64  %Background operators:
% 3.31/1.64  
% 3.31/1.64  
% 3.31/1.64  %Foreground operators:
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.31/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.31/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.31/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.31/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.31/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.31/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.31/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.64  
% 3.31/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.65  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 3.31/1.65  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.31/1.65  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 3.31/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.65  tff(c_40, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.65  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.65  tff(c_36, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.65  tff(c_138, plain, (![A_91, B_92, C_93]: (r2_hidden(k4_tarski('#skF_6'(A_91, B_92, C_93), A_91), C_93) | ~r2_hidden(A_91, k9_relat_1(C_93, B_92)) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.65  tff(c_144, plain, (![A_91, B_92, C_93, B_2]: (r2_hidden(k4_tarski('#skF_6'(A_91, B_92, C_93), A_91), B_2) | ~r1_tarski(C_93, B_2) | ~r2_hidden(A_91, k9_relat_1(C_93, B_92)) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.31/1.65  tff(c_28, plain, (![A_48, B_49, C_50]: (r2_hidden('#skF_6'(A_48, B_49, C_50), B_49) | ~r2_hidden(A_48, k9_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.65  tff(c_99, plain, (![D_82, A_83, B_84, E_85]: (r2_hidden(D_82, k9_relat_1(A_83, B_84)) | ~r2_hidden(E_85, B_84) | ~r2_hidden(k4_tarski(E_85, D_82), A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.65  tff(c_391, plain, (![B_211, A_214, D_210, C_213, A_212]: (r2_hidden(D_210, k9_relat_1(A_214, B_211)) | ~r2_hidden(k4_tarski('#skF_6'(A_212, B_211, C_213), D_210), A_214) | ~v1_relat_1(A_214) | ~r2_hidden(A_212, k9_relat_1(C_213, B_211)) | ~v1_relat_1(C_213))), inference(resolution, [status(thm)], [c_28, c_99])).
% 3.31/1.65  tff(c_503, plain, (![A_218, B_219, B_220, C_221]: (r2_hidden(A_218, k9_relat_1(B_219, B_220)) | ~v1_relat_1(B_219) | ~r1_tarski(C_221, B_219) | ~r2_hidden(A_218, k9_relat_1(C_221, B_220)) | ~v1_relat_1(C_221))), inference(resolution, [status(thm)], [c_144, c_391])).
% 3.31/1.65  tff(c_509, plain, (![A_218, B_220]: (r2_hidden(A_218, k9_relat_1('#skF_9', B_220)) | ~v1_relat_1('#skF_9') | ~r2_hidden(A_218, k9_relat_1('#skF_8', B_220)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_503])).
% 3.31/1.65  tff(c_517, plain, (![A_222, B_223]: (r2_hidden(A_222, k9_relat_1('#skF_9', B_223)) | ~r2_hidden(A_222, k9_relat_1('#skF_8', B_223)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_509])).
% 3.31/1.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.65  tff(c_691, plain, (![A_233, B_234]: (r1_tarski(A_233, k9_relat_1('#skF_9', B_234)) | ~r2_hidden('#skF_1'(A_233, k9_relat_1('#skF_9', B_234)), k9_relat_1('#skF_8', B_234)))), inference(resolution, [status(thm)], [c_517, c_4])).
% 3.31/1.65  tff(c_706, plain, (![B_234]: (r1_tarski(k9_relat_1('#skF_8', B_234), k9_relat_1('#skF_9', B_234)))), inference(resolution, [status(thm)], [c_6, c_691])).
% 3.31/1.65  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_8', '#skF_7'), k9_relat_1('#skF_9', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.65  tff(c_733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_706, c_34])).
% 3.31/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.65  
% 3.31/1.65  Inference rules
% 3.31/1.65  ----------------------
% 3.31/1.65  #Ref     : 0
% 3.31/1.65  #Sup     : 168
% 3.31/1.65  #Fact    : 0
% 3.31/1.65  #Define  : 0
% 3.31/1.65  #Split   : 1
% 3.31/1.65  #Chain   : 0
% 3.31/1.65  #Close   : 0
% 3.31/1.65  
% 3.31/1.65  Ordering : KBO
% 3.31/1.65  
% 3.31/1.65  Simplification rules
% 3.31/1.65  ----------------------
% 3.31/1.65  #Subsume      : 27
% 3.31/1.65  #Demod        : 9
% 3.31/1.65  #Tautology    : 3
% 3.31/1.65  #SimpNegUnit  : 0
% 3.31/1.65  #BackRed      : 1
% 3.31/1.65  
% 3.31/1.65  #Partial instantiations: 0
% 3.31/1.65  #Strategies tried      : 1
% 3.31/1.65  
% 3.31/1.65  Timing (in seconds)
% 3.31/1.65  ----------------------
% 3.31/1.65  Preprocessing        : 0.35
% 3.31/1.65  Parsing              : 0.19
% 3.31/1.65  CNF conversion       : 0.04
% 3.31/1.65  Main loop            : 0.51
% 3.31/1.65  Inferencing          : 0.19
% 3.31/1.65  Reduction            : 0.11
% 3.31/1.65  Demodulation         : 0.07
% 3.31/1.65  BG Simplification    : 0.03
% 3.31/1.65  Subsumption          : 0.15
% 3.31/1.65  Abstraction          : 0.02
% 3.31/1.66  MUC search           : 0.00
% 3.31/1.66  Cooper               : 0.00
% 3.31/1.66  Total                : 0.89
% 3.31/1.66  Index Insertion      : 0.00
% 3.31/1.66  Index Deletion       : 0.00
% 3.31/1.66  Index Matching       : 0.00
% 3.31/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
