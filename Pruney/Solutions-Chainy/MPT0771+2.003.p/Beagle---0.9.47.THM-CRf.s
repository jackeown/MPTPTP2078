%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:37 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
          & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(A_17,B_18)
      | ~ r2_hidden(A_17,k3_relat_1(k2_wellord1(C_19,B_18)))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_154,plain,(
    ! [C_51,B_52,B_53] :
      ( r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_51,B_52)),B_53),B_52)
      | ~ v1_relat_1(C_51)
      | r1_tarski(k3_relat_1(k2_wellord1(C_51,B_52)),B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_173,plain,(
    ! [C_54,B_55] :
      ( ~ v1_relat_1(C_54)
      | r1_tarski(k3_relat_1(k2_wellord1(C_54,B_55)),B_55) ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_47,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,k3_relat_1(C_24))
      | ~ r2_hidden(A_23,k3_relat_1(k2_wellord1(C_24,B_25)))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [C_39,B_40,B_41] :
      ( r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_39,B_40)),B_41),k3_relat_1(C_39))
      | ~ v1_relat_1(C_39)
      | r1_tarski(k3_relat_1(k2_wellord1(C_39,B_40)),B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_114,plain,(
    ! [C_42,B_43] :
      ( ~ v1_relat_1(C_42)
      | r1_tarski(k3_relat_1(k2_wellord1(C_42,B_43)),k3_relat_1(C_42)) ) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_12,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_3','#skF_2')),'#skF_2')
    | ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_3','#skF_2')),k3_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_3','#skF_2')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_122,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_58])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_122])).

tff(c_129,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1('#skF_3','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_182,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_129])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.93/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.19  
% 1.93/1.20  tff(f_47, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 1.93/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.20  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_wellord1)).
% 1.93/1.20  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.20  tff(c_27, plain, (![A_17, B_18, C_19]: (r2_hidden(A_17, B_18) | ~r2_hidden(A_17, k3_relat_1(k2_wellord1(C_19, B_18))) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.20  tff(c_154, plain, (![C_51, B_52, B_53]: (r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_51, B_52)), B_53), B_52) | ~v1_relat_1(C_51) | r1_tarski(k3_relat_1(k2_wellord1(C_51, B_52)), B_53))), inference(resolution, [status(thm)], [c_6, c_27])).
% 1.93/1.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.20  tff(c_173, plain, (![C_54, B_55]: (~v1_relat_1(C_54) | r1_tarski(k3_relat_1(k2_wellord1(C_54, B_55)), B_55))), inference(resolution, [status(thm)], [c_154, c_4])).
% 1.93/1.20  tff(c_47, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, k3_relat_1(C_24)) | ~r2_hidden(A_23, k3_relat_1(k2_wellord1(C_24, B_25))) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.93/1.20  tff(c_95, plain, (![C_39, B_40, B_41]: (r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_39, B_40)), B_41), k3_relat_1(C_39)) | ~v1_relat_1(C_39) | r1_tarski(k3_relat_1(k2_wellord1(C_39, B_40)), B_41))), inference(resolution, [status(thm)], [c_6, c_47])).
% 1.93/1.20  tff(c_114, plain, (![C_42, B_43]: (~v1_relat_1(C_42) | r1_tarski(k3_relat_1(k2_wellord1(C_42, B_43)), k3_relat_1(C_42)))), inference(resolution, [status(thm)], [c_95, c_4])).
% 1.93/1.20  tff(c_12, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_3', '#skF_2')), '#skF_2') | ~r1_tarski(k3_relat_1(k2_wellord1('#skF_3', '#skF_2')), k3_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.20  tff(c_58, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_3', '#skF_2')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12])).
% 1.93/1.20  tff(c_122, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_58])).
% 1.93/1.20  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_122])).
% 1.93/1.20  tff(c_129, plain, (~r1_tarski(k3_relat_1(k2_wellord1('#skF_3', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_12])).
% 1.93/1.20  tff(c_182, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_129])).
% 1.93/1.20  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_182])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 35
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 1
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 4
% 1.93/1.20  #Demod        : 3
% 1.93/1.20  #Tautology    : 2
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 0
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.25
% 1.93/1.20  Parsing              : 0.14
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.20
% 1.93/1.20  Inferencing          : 0.08
% 1.93/1.20  Reduction            : 0.04
% 1.93/1.20  Demodulation         : 0.03
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.05
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.20  MUC search           : 0.00
% 1.93/1.20  Cooper               : 0.00
% 1.93/1.20  Total                : 0.47
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
