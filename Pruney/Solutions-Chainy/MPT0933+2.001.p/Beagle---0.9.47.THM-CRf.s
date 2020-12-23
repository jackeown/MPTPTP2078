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
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  69 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( ( r2_hidden(C,B)
              & r2_hidden(A,B)
              & k1_mcart_1(C) = k1_mcart_1(A)
              & k2_mcart_1(C) = k2_mcart_1(A) )
           => C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(c_4,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    ! [A_4,B_5] :
      ( k4_tarski(k1_mcart_1(A_4),k2_mcart_1(A_4)) = A_4
      | ~ r2_hidden(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_30,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_6,plain,(
    k2_mcart_1('#skF_3') = k2_mcart_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    k1_mcart_1('#skF_3') = k1_mcart_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_33,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6,c_8,c_27])).

tff(c_38,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.06  
% 1.57/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.06  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.57/1.06  
% 1.57/1.06  %Foreground sorts:
% 1.57/1.06  
% 1.57/1.06  
% 1.57/1.06  %Background operators:
% 1.57/1.06  
% 1.57/1.06  
% 1.57/1.06  %Foreground operators:
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.57/1.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.57/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.06  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.57/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.06  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.57/1.06  
% 1.57/1.07  tff(f_45, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: ((((r2_hidden(C, B) & r2_hidden(A, B)) & (k1_mcart_1(C) = k1_mcart_1(A))) & (k2_mcart_1(C) = k2_mcart_1(A))) => (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_mcart_1)).
% 1.57/1.07  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.57/1.07  tff(c_4, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_23, plain, (![A_4, B_5]: (k4_tarski(k1_mcart_1(A_4), k2_mcart_1(A_4))=A_4 | ~r2_hidden(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.07  tff(c_25, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_23])).
% 1.57/1.07  tff(c_30, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_25])).
% 1.57/1.07  tff(c_6, plain, (k2_mcart_1('#skF_3')=k2_mcart_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_8, plain, (k1_mcart_1('#skF_3')=k1_mcart_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.57/1.07  tff(c_27, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.57/1.07  tff(c_33, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6, c_8, c_27])).
% 1.57/1.07  tff(c_38, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_33])).
% 1.57/1.07  tff(c_39, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_38])).
% 1.57/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.07  
% 1.57/1.07  Inference rules
% 1.57/1.07  ----------------------
% 1.57/1.07  #Ref     : 0
% 1.57/1.07  #Sup     : 8
% 1.57/1.07  #Fact    : 0
% 1.57/1.07  #Define  : 0
% 1.57/1.07  #Split   : 0
% 1.57/1.07  #Chain   : 0
% 1.57/1.07  #Close   : 0
% 1.57/1.07  
% 1.57/1.07  Ordering : KBO
% 1.57/1.07  
% 1.57/1.07  Simplification rules
% 1.57/1.07  ----------------------
% 1.57/1.07  #Subsume      : 0
% 1.57/1.07  #Demod        : 5
% 1.57/1.07  #Tautology    : 6
% 1.57/1.07  #SimpNegUnit  : 1
% 1.57/1.07  #BackRed      : 0
% 1.57/1.07  
% 1.57/1.07  #Partial instantiations: 0
% 1.57/1.07  #Strategies tried      : 1
% 1.57/1.07  
% 1.57/1.07  Timing (in seconds)
% 1.57/1.07  ----------------------
% 1.57/1.08  Preprocessing        : 0.25
% 1.57/1.08  Parsing              : 0.13
% 1.57/1.08  CNF conversion       : 0.02
% 1.57/1.08  Main loop            : 0.07
% 1.57/1.08  Inferencing          : 0.03
% 1.57/1.08  Reduction            : 0.02
% 1.57/1.08  Demodulation         : 0.02
% 1.57/1.08  BG Simplification    : 0.01
% 1.57/1.08  Subsumption          : 0.01
% 1.57/1.08  Abstraction          : 0.00
% 1.57/1.08  MUC search           : 0.00
% 1.57/1.08  Cooper               : 0.00
% 1.57/1.08  Total                : 0.34
% 1.57/1.08  Index Insertion      : 0.00
% 1.57/1.08  Index Deletion       : 0.00
% 1.57/1.08  Index Matching       : 0.00
% 1.57/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
