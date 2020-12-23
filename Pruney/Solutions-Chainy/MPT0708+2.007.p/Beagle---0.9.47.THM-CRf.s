%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:24 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  84 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_2',k10_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,k10_relat_1(B_10,k9_relat_1(B_10,A_9)))
      | ~ r1_tarski(A_9,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k10_relat_1(C_8,A_6),k10_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_22,B_23,B_24] :
      ( r2_hidden('#skF_1'(A_22,B_23),B_24)
      | ~ r1_tarski(A_22,B_24)
      | r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_27,B_28,B_29,B_30] :
      ( r2_hidden('#skF_1'(A_27,B_28),B_29)
      | ~ r1_tarski(B_30,B_29)
      | ~ r1_tarski(A_27,B_30)
      | r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_154,plain,(
    ! [B_51,B_53,C_50,A_52,A_54] :
      ( r2_hidden('#skF_1'(A_54,B_53),k10_relat_1(C_50,B_51))
      | ~ r1_tarski(A_54,k10_relat_1(C_50,A_52))
      | r1_tarski(A_54,B_53)
      | ~ r1_tarski(A_52,B_51)
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_350,plain,(
    ! [A_85,B_86,B_87,B_88] :
      ( r2_hidden('#skF_1'(A_85,B_86),k10_relat_1(B_87,B_88))
      | r1_tarski(A_85,B_86)
      | ~ r1_tarski(k9_relat_1(B_87,A_85),B_88)
      | ~ r1_tarski(A_85,k1_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_359,plain,(
    ! [A_89,B_90,B_91] :
      ( r1_tarski(A_89,k10_relat_1(B_90,B_91))
      | ~ r1_tarski(k9_relat_1(B_90,A_89),B_91)
      | ~ r1_tarski(A_89,k1_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_350,c_4])).

tff(c_390,plain,
    ( r1_tarski('#skF_2',k10_relat_1('#skF_4','#skF_3'))
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_359])).

tff(c_400,plain,(
    r1_tarski('#skF_2',k10_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_390])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n025.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:20:50 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.74/1.39  
% 2.74/1.39  %Foreground sorts:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Background operators:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Foreground operators:
% 2.74/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.39  
% 2.74/1.40  tff(f_55, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 2.74/1.40  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.74/1.40  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.74/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.40  tff(c_12, plain, (~r1_tarski('#skF_2', k10_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.40  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.41  tff(c_16, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.41  tff(c_14, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.74/1.41  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k10_relat_1(B_10, k9_relat_1(B_10, A_9))) | ~r1_tarski(A_9, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.41  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k10_relat_1(C_8, A_6), k10_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.41  tff(c_29, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.41  tff(c_34, plain, (![A_22, B_23, B_24]: (r2_hidden('#skF_1'(A_22, B_23), B_24) | ~r1_tarski(A_22, B_24) | r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_6, c_29])).
% 2.74/1.41  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.41  tff(c_44, plain, (![A_27, B_28, B_29, B_30]: (r2_hidden('#skF_1'(A_27, B_28), B_29) | ~r1_tarski(B_30, B_29) | ~r1_tarski(A_27, B_30) | r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_34, c_2])).
% 2.74/1.41  tff(c_154, plain, (![B_51, B_53, C_50, A_52, A_54]: (r2_hidden('#skF_1'(A_54, B_53), k10_relat_1(C_50, B_51)) | ~r1_tarski(A_54, k10_relat_1(C_50, A_52)) | r1_tarski(A_54, B_53) | ~r1_tarski(A_52, B_51) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_8, c_44])).
% 2.74/1.41  tff(c_350, plain, (![A_85, B_86, B_87, B_88]: (r2_hidden('#skF_1'(A_85, B_86), k10_relat_1(B_87, B_88)) | r1_tarski(A_85, B_86) | ~r1_tarski(k9_relat_1(B_87, A_85), B_88) | ~r1_tarski(A_85, k1_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.74/1.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.41  tff(c_359, plain, (![A_89, B_90, B_91]: (r1_tarski(A_89, k10_relat_1(B_90, B_91)) | ~r1_tarski(k9_relat_1(B_90, A_89), B_91) | ~r1_tarski(A_89, k1_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_350, c_4])).
% 2.74/1.41  tff(c_390, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_4', '#skF_3')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_359])).
% 2.74/1.41  tff(c_400, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_390])).
% 2.74/1.41  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_400])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 95
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 4
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 29
% 2.74/1.41  #Demod        : 3
% 2.74/1.41  #Tautology    : 2
% 2.74/1.41  #SimpNegUnit  : 1
% 2.74/1.41  #BackRed      : 0
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.41  Preprocessing        : 0.27
% 2.74/1.41  Parsing              : 0.15
% 2.74/1.41  CNF conversion       : 0.02
% 2.74/1.41  Main loop            : 0.38
% 2.74/1.41  Inferencing          : 0.14
% 2.74/1.41  Reduction            : 0.09
% 2.74/1.41  Demodulation         : 0.06
% 2.74/1.41  BG Simplification    : 0.01
% 2.74/1.41  Subsumption          : 0.11
% 2.74/1.41  Abstraction          : 0.02
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.68
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
