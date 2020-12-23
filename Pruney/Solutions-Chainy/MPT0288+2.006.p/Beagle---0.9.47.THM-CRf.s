%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:31 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  82 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_30])).

tff(c_12,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(C_21,'#skF_5'(A_6,k3_tarski(A_6),C_21))
      | ~ r2_hidden(C_21,k3_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_36,C_37] :
      ( r2_hidden('#skF_5'(A_36,k3_tarski(A_36),C_37),A_36)
      | ~ r2_hidden(C_37,k3_tarski(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden('#skF_5'(A_50,k3_tarski(A_50),C_51),B_52)
      | ~ r1_tarski(A_50,B_52)
      | ~ r2_hidden(C_51,k3_tarski(A_50)) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_845,plain,(
    ! [A_135,C_136,B_137,B_138] :
      ( r2_hidden('#skF_5'(A_135,k3_tarski(A_135),C_136),B_137)
      | ~ r1_tarski(B_138,B_137)
      | ~ r1_tarski(A_135,B_138)
      | ~ r2_hidden(C_136,k3_tarski(A_135)) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_858,plain,(
    ! [A_139,C_140] :
      ( r2_hidden('#skF_5'(A_139,k3_tarski(A_139),C_140),'#skF_7')
      | ~ r1_tarski(A_139,'#skF_6')
      | ~ r2_hidden(C_140,k3_tarski(A_139)) ) ),
    inference(resolution,[status(thm)],[c_28,c_845])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k3_tarski(A_6))
      | ~ r2_hidden(D_24,A_6)
      | ~ r2_hidden(C_21,D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1741,plain,(
    ! [C_197,A_198,C_199] :
      ( r2_hidden(C_197,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_197,'#skF_5'(A_198,k3_tarski(A_198),C_199))
      | ~ r1_tarski(A_198,'#skF_6')
      | ~ r2_hidden(C_199,k3_tarski(A_198)) ) ),
    inference(resolution,[status(thm)],[c_858,c_8])).

tff(c_1881,plain,(
    ! [C_200,A_201] :
      ( r2_hidden(C_200,k3_tarski('#skF_7'))
      | ~ r1_tarski(A_201,'#skF_6')
      | ~ r2_hidden(C_200,k3_tarski(A_201)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1741])).

tff(c_2005,plain,(
    ! [A_202,B_203] :
      ( r2_hidden('#skF_1'(k3_tarski(A_202),B_203),k3_tarski('#skF_7'))
      | ~ r1_tarski(A_202,'#skF_6')
      | r1_tarski(k3_tarski(A_202),B_203) ) ),
    inference(resolution,[status(thm)],[c_6,c_1881])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2023,plain,(
    ! [A_204] :
      ( ~ r1_tarski(A_204,'#skF_6')
      | r1_tarski(k3_tarski(A_204),k3_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2005,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k3_tarski('#skF_6'),k3_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2040,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2023,c_26])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.89  
% 4.53/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.90  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 4.53/1.90  
% 4.53/1.90  %Foreground sorts:
% 4.53/1.90  
% 4.53/1.90  
% 4.53/1.90  %Background operators:
% 4.53/1.90  
% 4.53/1.90  
% 4.53/1.90  %Foreground operators:
% 4.53/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.53/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.53/1.90  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.53/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.53/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.53/1.90  
% 4.53/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.53/1.91  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 4.53/1.91  tff(f_47, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 4.53/1.91  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.91  tff(c_30, plain, (![A_27, B_28]: (~r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.91  tff(c_35, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_30])).
% 4.53/1.91  tff(c_12, plain, (![C_21, A_6]: (r2_hidden(C_21, '#skF_5'(A_6, k3_tarski(A_6), C_21)) | ~r2_hidden(C_21, k3_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.53/1.91  tff(c_28, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.53/1.91  tff(c_45, plain, (![A_36, C_37]: (r2_hidden('#skF_5'(A_36, k3_tarski(A_36), C_37), A_36) | ~r2_hidden(C_37, k3_tarski(A_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.53/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.91  tff(c_106, plain, (![A_50, C_51, B_52]: (r2_hidden('#skF_5'(A_50, k3_tarski(A_50), C_51), B_52) | ~r1_tarski(A_50, B_52) | ~r2_hidden(C_51, k3_tarski(A_50)))), inference(resolution, [status(thm)], [c_45, c_2])).
% 4.53/1.91  tff(c_845, plain, (![A_135, C_136, B_137, B_138]: (r2_hidden('#skF_5'(A_135, k3_tarski(A_135), C_136), B_137) | ~r1_tarski(B_138, B_137) | ~r1_tarski(A_135, B_138) | ~r2_hidden(C_136, k3_tarski(A_135)))), inference(resolution, [status(thm)], [c_106, c_2])).
% 4.53/1.91  tff(c_858, plain, (![A_139, C_140]: (r2_hidden('#skF_5'(A_139, k3_tarski(A_139), C_140), '#skF_7') | ~r1_tarski(A_139, '#skF_6') | ~r2_hidden(C_140, k3_tarski(A_139)))), inference(resolution, [status(thm)], [c_28, c_845])).
% 4.53/1.91  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k3_tarski(A_6)) | ~r2_hidden(D_24, A_6) | ~r2_hidden(C_21, D_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.53/1.91  tff(c_1741, plain, (![C_197, A_198, C_199]: (r2_hidden(C_197, k3_tarski('#skF_7')) | ~r2_hidden(C_197, '#skF_5'(A_198, k3_tarski(A_198), C_199)) | ~r1_tarski(A_198, '#skF_6') | ~r2_hidden(C_199, k3_tarski(A_198)))), inference(resolution, [status(thm)], [c_858, c_8])).
% 4.53/1.91  tff(c_1881, plain, (![C_200, A_201]: (r2_hidden(C_200, k3_tarski('#skF_7')) | ~r1_tarski(A_201, '#skF_6') | ~r2_hidden(C_200, k3_tarski(A_201)))), inference(resolution, [status(thm)], [c_12, c_1741])).
% 4.53/1.91  tff(c_2005, plain, (![A_202, B_203]: (r2_hidden('#skF_1'(k3_tarski(A_202), B_203), k3_tarski('#skF_7')) | ~r1_tarski(A_202, '#skF_6') | r1_tarski(k3_tarski(A_202), B_203))), inference(resolution, [status(thm)], [c_6, c_1881])).
% 4.53/1.91  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.53/1.91  tff(c_2023, plain, (![A_204]: (~r1_tarski(A_204, '#skF_6') | r1_tarski(k3_tarski(A_204), k3_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_2005, c_4])).
% 4.53/1.91  tff(c_26, plain, (~r1_tarski(k3_tarski('#skF_6'), k3_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.53/1.91  tff(c_2040, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_2023, c_26])).
% 4.53/1.91  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_2040])).
% 4.53/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.91  
% 4.53/1.91  Inference rules
% 4.53/1.91  ----------------------
% 4.53/1.91  #Ref     : 0
% 4.53/1.91  #Sup     : 515
% 4.53/1.91  #Fact    : 0
% 4.53/1.91  #Define  : 0
% 4.53/1.91  #Split   : 1
% 4.53/1.91  #Chain   : 0
% 4.53/1.91  #Close   : 0
% 4.53/1.91  
% 4.53/1.91  Ordering : KBO
% 4.53/1.91  
% 4.53/1.91  Simplification rules
% 4.53/1.91  ----------------------
% 4.53/1.91  #Subsume      : 34
% 4.53/1.91  #Demod        : 1
% 4.53/1.91  #Tautology    : 5
% 4.53/1.91  #SimpNegUnit  : 0
% 4.53/1.91  #BackRed      : 0
% 4.53/1.91  
% 4.53/1.91  #Partial instantiations: 0
% 4.53/1.91  #Strategies tried      : 1
% 4.53/1.91  
% 4.53/1.91  Timing (in seconds)
% 4.53/1.91  ----------------------
% 4.82/1.91  Preprocessing        : 0.29
% 4.82/1.91  Parsing              : 0.15
% 4.82/1.91  CNF conversion       : 0.03
% 4.82/1.91  Main loop            : 0.79
% 4.82/1.91  Inferencing          : 0.25
% 4.82/1.91  Reduction            : 0.15
% 4.82/1.91  Demodulation         : 0.10
% 4.82/1.91  BG Simplification    : 0.04
% 4.82/1.91  Subsumption          : 0.28
% 4.82/1.91  Abstraction          : 0.05
% 4.82/1.91  MUC search           : 0.00
% 4.82/1.91  Cooper               : 0.00
% 4.82/1.91  Total                : 1.10
% 4.82/1.91  Index Insertion      : 0.00
% 4.82/1.91  Index Deletion       : 0.00
% 4.82/1.91  Index Matching       : 0.00
% 4.82/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
