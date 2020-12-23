%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A) )
       => ! [C] :
            ( r2_hidden(C,k2_relat_1(B))
           => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_12,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [B_19] :
      ( r2_hidden('#skF_4',B_19)
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_19) ) ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_39,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_4',A_6)
      | ~ v5_relat_1('#skF_3',A_6)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_35])).

tff(c_49,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_4',A_20)
      | ~ v5_relat_1('#skF_3',A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_39])).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  
% 1.55/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.07  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.55/1.07  
% 1.55/1.07  %Foreground sorts:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Background operators:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Foreground operators:
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.55/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.07  tff('#skF_4', type, '#skF_4': $i).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.55/1.07  
% 1.55/1.08  tff(f_48, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 1.55/1.08  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.55/1.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.55/1.08  tff(c_12, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.55/1.08  tff(c_16, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.55/1.08  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.55/1.08  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.08  tff(c_14, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.08  tff(c_28, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.08  tff(c_35, plain, (![B_19]: (r2_hidden('#skF_4', B_19) | ~r1_tarski(k2_relat_1('#skF_3'), B_19))), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.62/1.08  tff(c_39, plain, (![A_6]: (r2_hidden('#skF_4', A_6) | ~v5_relat_1('#skF_3', A_6) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_35])).
% 1.62/1.08  tff(c_49, plain, (![A_20]: (r2_hidden('#skF_4', A_20) | ~v5_relat_1('#skF_3', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_39])).
% 1.62/1.08  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_49])).
% 1.62/1.08  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_52])).
% 1.62/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  Inference rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Ref     : 0
% 1.62/1.08  #Sup     : 6
% 1.62/1.08  #Fact    : 0
% 1.62/1.08  #Define  : 0
% 1.62/1.08  #Split   : 0
% 1.62/1.08  #Chain   : 0
% 1.62/1.08  #Close   : 0
% 1.62/1.08  
% 1.62/1.08  Ordering : KBO
% 1.62/1.08  
% 1.62/1.08  Simplification rules
% 1.62/1.08  ----------------------
% 1.62/1.08  #Subsume      : 0
% 1.62/1.08  #Demod        : 2
% 1.62/1.08  #Tautology    : 1
% 1.62/1.08  #SimpNegUnit  : 1
% 1.62/1.08  #BackRed      : 0
% 1.62/1.08  
% 1.62/1.08  #Partial instantiations: 0
% 1.62/1.08  #Strategies tried      : 1
% 1.62/1.08  
% 1.62/1.08  Timing (in seconds)
% 1.62/1.08  ----------------------
% 1.62/1.08  Preprocessing        : 0.24
% 1.62/1.08  Parsing              : 0.14
% 1.62/1.08  CNF conversion       : 0.02
% 1.62/1.08  Main loop            : 0.09
% 1.62/1.08  Inferencing          : 0.04
% 1.62/1.08  Reduction            : 0.02
% 1.62/1.08  Demodulation         : 0.02
% 1.62/1.08  BG Simplification    : 0.01
% 1.62/1.08  Subsumption          : 0.01
% 1.62/1.08  Abstraction          : 0.00
% 1.62/1.08  MUC search           : 0.00
% 1.62/1.08  Cooper               : 0.00
% 1.62/1.08  Total                : 0.36
% 1.62/1.08  Index Insertion      : 0.00
% 1.62/1.08  Index Deletion       : 0.00
% 1.62/1.08  Index Matching       : 0.00
% 1.62/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
