%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:35 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  30 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
       => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

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

tff(c_49,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,k1_relat_1(C_24))
      | ~ r2_hidden(A_23,k1_relat_1(k7_relat_1(C_24,B_25)))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [C_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_42,B_43)),B_44),k1_relat_1(C_42))
      | ~ v1_relat_1(C_42)
      | r1_tarski(k1_relat_1(k7_relat_1(C_42,B_43)),B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [C_45,B_46] :
      ( ~ v1_relat_1(C_45)
      | r1_tarski(k1_relat_1(k7_relat_1(C_45,B_46)),k1_relat_1(C_45)) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_14,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_14])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:40:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  
% 1.86/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.16  
% 1.86/1.16  %Foreground sorts:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Background operators:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Foreground operators:
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.16  
% 1.86/1.17  tff(f_45, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 1.86/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.86/1.17  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 1.86/1.17  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.17  tff(c_49, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, k1_relat_1(C_24)) | ~r2_hidden(A_23, k1_relat_1(k7_relat_1(C_24, B_25))) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.86/1.17  tff(c_113, plain, (![C_42, B_43, B_44]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(C_42, B_43)), B_44), k1_relat_1(C_42)) | ~v1_relat_1(C_42) | r1_tarski(k1_relat_1(k7_relat_1(C_42, B_43)), B_44))), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.86/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.17  tff(c_132, plain, (![C_45, B_46]: (~v1_relat_1(C_45) | r1_tarski(k1_relat_1(k7_relat_1(C_45, B_46)), k1_relat_1(C_45)))), inference(resolution, [status(thm)], [c_113, c_4])).
% 1.86/1.17  tff(c_14, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.17  tff(c_140, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_14])).
% 1.86/1.17  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_140])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 27
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 3
% 1.86/1.17  #Demod        : 1
% 1.86/1.17  #Tautology    : 3
% 1.86/1.17  #SimpNegUnit  : 0
% 1.86/1.17  #BackRed      : 0
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.17  Preprocessing        : 0.24
% 1.86/1.17  Parsing              : 0.13
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.16
% 1.86/1.17  Inferencing          : 0.06
% 1.86/1.17  Reduction            : 0.03
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.05
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.43
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
