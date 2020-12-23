%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :   16 (  24 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(C,B)
           => k9_relat_1(A,C) = k9_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ! [A_8,C_9,B_10] :
      ( k9_relat_1(k7_relat_1(A_8,C_9),B_10) = k9_relat_1(A_8,B_10)
      | ~ r1_tarski(B_10,C_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k9_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11,c_4])).

tff(c_25,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6,c_17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:36:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.06  
% 1.47/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.07  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.47/1.07  
% 1.47/1.07  %Foreground sorts:
% 1.47/1.07  
% 1.47/1.07  
% 1.47/1.07  %Background operators:
% 1.47/1.07  
% 1.47/1.07  
% 1.47/1.07  %Foreground operators:
% 1.47/1.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.47/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.47/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.47/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.47/1.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.47/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.47/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.47/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.07  
% 1.47/1.07  tff(f_42, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(C, B) => (k9_relat_1(A, C) = k9_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_2)).
% 1.47/1.07  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 1.47/1.07  tff(c_10, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.47/1.07  tff(c_6, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.47/1.07  tff(c_11, plain, (![A_8, C_9, B_10]: (k9_relat_1(k7_relat_1(A_8, C_9), B_10)=k9_relat_1(A_8, B_10) | ~r1_tarski(B_10, C_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.47/1.07  tff(c_4, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k9_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.47/1.07  tff(c_17, plain, (~r1_tarski('#skF_3', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11, c_4])).
% 1.47/1.07  tff(c_25, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_6, c_17])).
% 1.47/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.07  
% 1.47/1.07  Inference rules
% 1.47/1.07  ----------------------
% 1.47/1.07  #Ref     : 0
% 1.47/1.07  #Sup     : 3
% 1.47/1.07  #Fact    : 0
% 1.47/1.07  #Define  : 0
% 1.47/1.07  #Split   : 0
% 1.47/1.07  #Chain   : 0
% 1.47/1.07  #Close   : 0
% 1.47/1.07  
% 1.47/1.07  Ordering : KBO
% 1.47/1.07  
% 1.47/1.07  Simplification rules
% 1.47/1.07  ----------------------
% 1.47/1.07  #Subsume      : 0
% 1.47/1.07  #Demod        : 2
% 1.47/1.07  #Tautology    : 1
% 1.47/1.07  #SimpNegUnit  : 0
% 1.47/1.07  #BackRed      : 0
% 1.47/1.07  
% 1.47/1.07  #Partial instantiations: 0
% 1.47/1.07  #Strategies tried      : 1
% 1.47/1.07  
% 1.47/1.07  Timing (in seconds)
% 1.47/1.07  ----------------------
% 1.47/1.08  Preprocessing        : 0.23
% 1.47/1.08  Parsing              : 0.12
% 1.47/1.08  CNF conversion       : 0.01
% 1.47/1.08  Main loop            : 0.06
% 1.47/1.08  Inferencing          : 0.03
% 1.47/1.08  Reduction            : 0.02
% 1.47/1.08  Demodulation         : 0.01
% 1.47/1.08  BG Simplification    : 0.01
% 1.47/1.08  Subsumption          : 0.00
% 1.47/1.08  Abstraction          : 0.00
% 1.47/1.08  MUC search           : 0.00
% 1.47/1.08  Cooper               : 0.00
% 1.47/1.08  Total                : 0.31
% 1.47/1.08  Index Insertion      : 0.00
% 1.47/1.08  Index Deletion       : 0.00
% 1.47/1.08  Index Matching       : 0.00
% 1.47/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
