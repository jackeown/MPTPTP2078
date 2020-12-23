%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_10,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_19,B_20)),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    r2_hidden('#skF_2',k2_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_29,plain,(
    ! [C_15,B_16,A_17] :
      ( r2_hidden(C_15,B_16)
      | ~ r2_hidden(C_15,A_17)
      | ~ r1_tarski(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_2',B_16)
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_4','#skF_3')),B_16) ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_47,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_35])).

tff(c_50,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.76/1.19  
% 1.76/1.19  %Foreground sorts:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Background operators:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Foreground operators:
% 1.76/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.76/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.76/1.19  
% 1.76/1.20  tff(f_53, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_1)).
% 1.76/1.20  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 1.76/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.76/1.20  tff(c_10, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.20  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.20  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.20  tff(c_43, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k5_relat_1(A_19, B_20)), k2_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.76/1.20  tff(c_12, plain, (r2_hidden('#skF_2', k2_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.20  tff(c_29, plain, (![C_15, B_16, A_17]: (r2_hidden(C_15, B_16) | ~r2_hidden(C_15, A_17) | ~r1_tarski(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.76/1.20  tff(c_35, plain, (![B_16]: (r2_hidden('#skF_2', B_16) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_4', '#skF_3')), B_16))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.76/1.20  tff(c_47, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_43, c_35])).
% 1.76/1.20  tff(c_50, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_47])).
% 1.76/1.20  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_50])).
% 1.76/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.20  
% 1.76/1.20  Inference rules
% 1.76/1.20  ----------------------
% 1.76/1.20  #Ref     : 0
% 1.76/1.20  #Sup     : 5
% 1.76/1.20  #Fact    : 0
% 1.76/1.20  #Define  : 0
% 1.76/1.20  #Split   : 0
% 1.76/1.20  #Chain   : 0
% 1.76/1.20  #Close   : 0
% 1.76/1.20  
% 1.76/1.20  Ordering : KBO
% 1.76/1.20  
% 1.76/1.20  Simplification rules
% 1.76/1.20  ----------------------
% 1.76/1.20  #Subsume      : 0
% 1.76/1.20  #Demod        : 3
% 1.76/1.20  #Tautology    : 1
% 1.76/1.20  #SimpNegUnit  : 1
% 1.76/1.20  #BackRed      : 0
% 1.76/1.20  
% 1.76/1.20  #Partial instantiations: 0
% 1.76/1.20  #Strategies tried      : 1
% 1.76/1.20  
% 1.76/1.20  Timing (in seconds)
% 1.76/1.20  ----------------------
% 1.76/1.21  Preprocessing        : 0.28
% 1.76/1.21  Parsing              : 0.15
% 1.76/1.21  CNF conversion       : 0.02
% 1.76/1.21  Main loop            : 0.09
% 1.76/1.21  Inferencing          : 0.04
% 1.76/1.21  Reduction            : 0.02
% 1.76/1.21  Demodulation         : 0.02
% 1.76/1.21  BG Simplification    : 0.01
% 1.76/1.21  Subsumption          : 0.01
% 1.76/1.21  Abstraction          : 0.00
% 1.76/1.21  MUC search           : 0.00
% 1.76/1.21  Cooper               : 0.00
% 1.76/1.21  Total                : 0.39
% 1.76/1.21  Index Insertion      : 0.00
% 1.76/1.21  Index Deletion       : 0.00
% 1.76/1.21  Index Matching       : 0.00
% 1.76/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
