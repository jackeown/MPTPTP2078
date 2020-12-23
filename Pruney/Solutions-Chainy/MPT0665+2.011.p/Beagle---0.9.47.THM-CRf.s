%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  96 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_25,C_27] :
      ( r2_hidden(k4_tarski(A_25,k1_funct_1(C_27,A_25)),C_27)
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ! [D_56,E_57,A_58,B_59] :
      ( r2_hidden(k4_tarski(D_56,E_57),k7_relat_1(A_58,B_59))
      | ~ r2_hidden(k4_tarski(D_56,E_57),A_58)
      | ~ r2_hidden(D_56,B_59)
      | ~ v1_relat_1(k7_relat_1(A_58,B_59))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [B_21,C_22,A_20] :
      ( r2_hidden(B_21,k2_relat_1(C_22))
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_109,plain,(
    ! [E_64,A_65,B_66,D_67] :
      ( r2_hidden(E_64,k2_relat_1(k7_relat_1(A_65,B_66)))
      | ~ r2_hidden(k4_tarski(D_67,E_64),A_65)
      | ~ r2_hidden(D_67,B_66)
      | ~ v1_relat_1(k7_relat_1(A_65,B_66))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_81,c_20])).

tff(c_195,plain,(
    ! [C_80,A_81,B_82] :
      ( r2_hidden(k1_funct_1(C_80,A_81),k2_relat_1(k7_relat_1(C_80,B_82)))
      | ~ r2_hidden(A_81,B_82)
      | ~ v1_relat_1(k7_relat_1(C_80,B_82))
      | ~ r2_hidden(A_81,k1_relat_1(C_80))
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_28,c_109])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_198,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_195,c_34])).

tff(c_201,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_198])).

tff(c_204,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.31/1.33  
% 2.31/1.33  %Foreground sorts:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Background operators:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Foreground operators:
% 2.31/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.31/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.33  
% 2.31/1.34  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 2.31/1.34  tff(f_55, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.31/1.34  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.31/1.34  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 2.31/1.34  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.31/1.34  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.34  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.34  tff(c_26, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.34  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.34  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.34  tff(c_28, plain, (![A_25, C_27]: (r2_hidden(k4_tarski(A_25, k1_funct_1(C_27, A_25)), C_27) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.34  tff(c_81, plain, (![D_56, E_57, A_58, B_59]: (r2_hidden(k4_tarski(D_56, E_57), k7_relat_1(A_58, B_59)) | ~r2_hidden(k4_tarski(D_56, E_57), A_58) | ~r2_hidden(D_56, B_59) | ~v1_relat_1(k7_relat_1(A_58, B_59)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.34  tff(c_20, plain, (![B_21, C_22, A_20]: (r2_hidden(B_21, k2_relat_1(C_22)) | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.31/1.34  tff(c_109, plain, (![E_64, A_65, B_66, D_67]: (r2_hidden(E_64, k2_relat_1(k7_relat_1(A_65, B_66))) | ~r2_hidden(k4_tarski(D_67, E_64), A_65) | ~r2_hidden(D_67, B_66) | ~v1_relat_1(k7_relat_1(A_65, B_66)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_81, c_20])).
% 2.31/1.34  tff(c_195, plain, (![C_80, A_81, B_82]: (r2_hidden(k1_funct_1(C_80, A_81), k2_relat_1(k7_relat_1(C_80, B_82))) | ~r2_hidden(A_81, B_82) | ~v1_relat_1(k7_relat_1(C_80, B_82)) | ~r2_hidden(A_81, k1_relat_1(C_80)) | ~v1_funct_1(C_80) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_28, c_109])).
% 2.31/1.34  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.31/1.34  tff(c_198, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_195, c_34])).
% 2.31/1.34  tff(c_201, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_198])).
% 2.31/1.34  tff(c_204, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_201])).
% 2.31/1.34  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_204])).
% 2.31/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  
% 2.31/1.34  Inference rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Ref     : 0
% 2.31/1.34  #Sup     : 34
% 2.31/1.34  #Fact    : 0
% 2.31/1.34  #Define  : 0
% 2.31/1.34  #Split   : 0
% 2.31/1.34  #Chain   : 0
% 2.31/1.34  #Close   : 0
% 2.31/1.34  
% 2.31/1.34  Ordering : KBO
% 2.31/1.34  
% 2.31/1.34  Simplification rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Subsume      : 1
% 2.31/1.34  #Demod        : 6
% 2.31/1.34  #Tautology    : 5
% 2.31/1.34  #SimpNegUnit  : 0
% 2.31/1.34  #BackRed      : 0
% 2.31/1.34  
% 2.31/1.34  #Partial instantiations: 0
% 2.31/1.34  #Strategies tried      : 1
% 2.31/1.34  
% 2.31/1.34  Timing (in seconds)
% 2.31/1.34  ----------------------
% 2.31/1.35  Preprocessing        : 0.31
% 2.31/1.35  Parsing              : 0.17
% 2.31/1.35  CNF conversion       : 0.03
% 2.31/1.35  Main loop            : 0.22
% 2.31/1.35  Inferencing          : 0.09
% 2.31/1.35  Reduction            : 0.05
% 2.31/1.35  Demodulation         : 0.04
% 2.31/1.35  BG Simplification    : 0.02
% 2.31/1.35  Subsumption          : 0.05
% 2.31/1.35  Abstraction          : 0.01
% 2.31/1.35  MUC search           : 0.00
% 2.31/1.35  Cooper               : 0.00
% 2.31/1.35  Total                : 0.55
% 2.31/1.35  Index Insertion      : 0.00
% 2.31/1.35  Index Deletion       : 0.00
% 2.31/1.35  Index Matching       : 0.00
% 2.31/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
