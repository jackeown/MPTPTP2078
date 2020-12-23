%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:35 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

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
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

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
      | ~ r2_hidden(A_17,k1_relat_1(k7_relat_1(C_19,B_18)))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [C_33,B_34,B_35] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_33,B_34)),B_35),B_34)
      | ~ v1_relat_1(C_33)
      | r1_tarski(k1_relat_1(k7_relat_1(C_33,B_34)),B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [C_36,B_37] :
      ( ~ v1_relat_1(C_36)
      | r1_tarski(k1_relat_1(k7_relat_1(C_36,B_37)),B_37) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_14,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:58:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.60/1.13  
% 1.60/1.13  %Foreground sorts:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Background operators:
% 1.60/1.13  
% 1.60/1.13  
% 1.60/1.13  %Foreground operators:
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.60/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.13  
% 1.60/1.13  tff(f_45, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.60/1.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.60/1.13  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 1.60/1.13  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.13  tff(c_29, plain, (![A_17, B_18, C_19]: (r2_hidden(A_17, B_18) | ~r2_hidden(A_17, k1_relat_1(k7_relat_1(C_19, B_18))) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.13  tff(c_81, plain, (![C_33, B_34, B_35]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_33, B_34)), B_35), B_34) | ~v1_relat_1(C_33) | r1_tarski(k1_relat_1(k7_relat_1(C_33, B_34)), B_35))), inference(resolution, [status(thm)], [c_6, c_29])).
% 1.60/1.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.13  tff(c_100, plain, (![C_36, B_37]: (~v1_relat_1(C_36) | r1_tarski(k1_relat_1(k7_relat_1(C_36, B_37)), B_37))), inference(resolution, [status(thm)], [c_81, c_4])).
% 1.60/1.13  tff(c_14, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.13  tff(c_105, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_14])).
% 1.60/1.13  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_105])).
% 1.60/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  Inference rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Ref     : 0
% 1.60/1.13  #Sup     : 19
% 1.60/1.13  #Fact    : 0
% 1.60/1.13  #Define  : 0
% 1.60/1.13  #Split   : 0
% 1.60/1.14  #Chain   : 0
% 1.60/1.14  #Close   : 0
% 1.60/1.14  
% 1.60/1.14  Ordering : KBO
% 1.60/1.14  
% 1.60/1.14  Simplification rules
% 1.60/1.14  ----------------------
% 1.60/1.14  #Subsume      : 1
% 1.60/1.14  #Demod        : 1
% 1.60/1.14  #Tautology    : 3
% 1.60/1.14  #SimpNegUnit  : 0
% 1.60/1.14  #BackRed      : 0
% 1.60/1.14  
% 1.60/1.14  #Partial instantiations: 0
% 1.60/1.14  #Strategies tried      : 1
% 1.60/1.14  
% 1.60/1.14  Timing (in seconds)
% 1.60/1.14  ----------------------
% 1.77/1.14  Preprocessing        : 0.24
% 1.77/1.14  Parsing              : 0.14
% 1.77/1.14  CNF conversion       : 0.02
% 1.77/1.14  Main loop            : 0.14
% 1.77/1.14  Inferencing          : 0.06
% 1.77/1.14  Reduction            : 0.03
% 1.77/1.14  Demodulation         : 0.02
% 1.77/1.14  BG Simplification    : 0.01
% 1.77/1.14  Subsumption          : 0.03
% 1.77/1.14  Abstraction          : 0.01
% 1.77/1.14  MUC search           : 0.00
% 1.77/1.14  Cooper               : 0.00
% 1.77/1.14  Total                : 0.41
% 1.77/1.14  Index Insertion      : 0.00
% 1.77/1.14  Index Deletion       : 0.00
% 1.77/1.14  Index Matching       : 0.00
% 1.77/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
