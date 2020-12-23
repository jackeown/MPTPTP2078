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
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  30 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

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
     => ( r2_hidden(A,k2_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(A_17,B_18)
      | ~ r2_hidden(A_17,k2_relat_1(k8_relat_1(B_18,C_19)))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [B_33,C_34,B_35] :
      ( r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_33,C_34)),B_35),B_33)
      | ~ v1_relat_1(C_34)
      | r1_tarski(k2_relat_1(k8_relat_1(B_33,C_34)),B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [C_36,B_37] :
      ( ~ v1_relat_1(C_36)
      | r1_tarski(k2_relat_1(k8_relat_1(B_37,C_36)),B_37) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_14,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.14  
% 1.75/1.14  %Foreground sorts:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Background operators:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Foreground operators:
% 1.75/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.75/1.14  
% 1.75/1.14  tff(f_45, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 1.75/1.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.75/1.14  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k2_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, B) & r2_hidden(A, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_relat_1)).
% 1.75/1.14  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.75/1.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.14  tff(c_29, plain, (![A_17, B_18, C_19]: (r2_hidden(A_17, B_18) | ~r2_hidden(A_17, k2_relat_1(k8_relat_1(B_18, C_19))) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.75/1.14  tff(c_81, plain, (![B_33, C_34, B_35]: (r2_hidden('#skF_1'(k2_relat_1(k8_relat_1(B_33, C_34)), B_35), B_33) | ~v1_relat_1(C_34) | r1_tarski(k2_relat_1(k8_relat_1(B_33, C_34)), B_35))), inference(resolution, [status(thm)], [c_6, c_29])).
% 1.75/1.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.14  tff(c_100, plain, (![C_36, B_37]: (~v1_relat_1(C_36) | r1_tarski(k2_relat_1(k8_relat_1(B_37, C_36)), B_37))), inference(resolution, [status(thm)], [c_81, c_4])).
% 1.75/1.14  tff(c_14, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_3')), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.75/1.14  tff(c_105, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_14])).
% 1.75/1.14  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_105])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 19
% 1.75/1.15  #Fact    : 0
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 0
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 1
% 1.75/1.15  #Demod        : 1
% 1.75/1.15  #Tautology    : 3
% 1.75/1.15  #SimpNegUnit  : 0
% 1.75/1.15  #BackRed      : 0
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.15  Preprocessing        : 0.25
% 1.75/1.15  Parsing              : 0.14
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.15  Main loop            : 0.13
% 1.75/1.15  Inferencing          : 0.05
% 1.75/1.15  Reduction            : 0.03
% 1.75/1.15  Demodulation         : 0.02
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.03
% 1.75/1.15  Abstraction          : 0.01
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.40
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
