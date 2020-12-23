%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:47 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  76 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v4_relat_1(C,A) )
           => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_12,plain,(
    ~ v4_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [C_16,B_17,A_18] :
      ( r2_hidden(C_16,B_17)
      | ~ r2_hidden(C_16,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_22,B_23,B_24] :
      ( r2_hidden('#skF_1'(A_22,B_23),B_24)
      | ~ r1_tarski(A_22,B_24)
      | r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_25,B_26,B_27,B_28] :
      ( r2_hidden('#skF_1'(A_25,B_26),B_27)
      | ~ r1_tarski(B_28,B_27)
      | ~ r1_tarski(A_25,B_28)
      | r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_62,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),'#skF_3')
      | ~ r1_tarski(A_29,'#skF_2')
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_31] :
      ( ~ r1_tarski(A_31,'#skF_2')
      | r1_tarski(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_92,plain,(
    ! [B_36] :
      ( r1_tarski(k1_relat_1(B_36),'#skF_3')
      | ~ v4_relat_1(B_36,'#skF_2')
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_10,c_71])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [B_37] :
      ( v4_relat_1(B_37,'#skF_3')
      | ~ v4_relat_1(B_37,'#skF_2')
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_103,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_106,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_103])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  %$ v4_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.60/1.14  
% 1.60/1.14  %Foreground sorts:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Background operators:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Foreground operators:
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.60/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.14  
% 1.60/1.15  tff(f_48, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 1.60/1.15  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.60/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.60/1.15  tff(c_12, plain, (~v4_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.15  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.15  tff(c_14, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.15  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.15  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_28, plain, (![C_16, B_17, A_18]: (r2_hidden(C_16, B_17) | ~r2_hidden(C_16, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_43, plain, (![A_22, B_23, B_24]: (r2_hidden('#skF_1'(A_22, B_23), B_24) | ~r1_tarski(A_22, B_24) | r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.60/1.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_52, plain, (![A_25, B_26, B_27, B_28]: (r2_hidden('#skF_1'(A_25, B_26), B_27) | ~r1_tarski(B_28, B_27) | ~r1_tarski(A_25, B_28) | r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.60/1.15  tff(c_62, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), '#skF_3') | ~r1_tarski(A_29, '#skF_2') | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_18, c_52])).
% 1.60/1.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_71, plain, (![A_31]: (~r1_tarski(A_31, '#skF_2') | r1_tarski(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_4])).
% 1.60/1.15  tff(c_92, plain, (![B_36]: (r1_tarski(k1_relat_1(B_36), '#skF_3') | ~v4_relat_1(B_36, '#skF_2') | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_10, c_71])).
% 1.60/1.15  tff(c_8, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.15  tff(c_100, plain, (![B_37]: (v4_relat_1(B_37, '#skF_3') | ~v4_relat_1(B_37, '#skF_2') | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_92, c_8])).
% 1.60/1.15  tff(c_103, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_100])).
% 1.60/1.15  tff(c_106, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_103])).
% 1.60/1.15  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_106])).
% 1.60/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  Inference rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Ref     : 0
% 1.60/1.15  #Sup     : 18
% 1.60/1.15  #Fact    : 0
% 1.60/1.15  #Define  : 0
% 1.60/1.15  #Split   : 0
% 1.60/1.15  #Chain   : 0
% 1.60/1.15  #Close   : 0
% 1.60/1.15  
% 1.60/1.15  Ordering : KBO
% 1.60/1.15  
% 1.60/1.15  Simplification rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Subsume      : 1
% 1.60/1.15  #Demod        : 2
% 1.60/1.15  #Tautology    : 3
% 1.60/1.15  #SimpNegUnit  : 1
% 1.60/1.15  #BackRed      : 0
% 1.60/1.15  
% 1.60/1.15  #Partial instantiations: 0
% 1.60/1.15  #Strategies tried      : 1
% 1.60/1.15  
% 1.60/1.15  Timing (in seconds)
% 1.60/1.15  ----------------------
% 1.60/1.16  Preprocessing        : 0.25
% 1.60/1.16  Parsing              : 0.14
% 1.60/1.16  CNF conversion       : 0.02
% 1.60/1.16  Main loop            : 0.15
% 1.60/1.16  Inferencing          : 0.06
% 1.60/1.16  Reduction            : 0.03
% 1.60/1.16  Demodulation         : 0.02
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.03
% 1.60/1.16  Abstraction          : 0.01
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.42
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
