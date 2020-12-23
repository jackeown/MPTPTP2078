%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  41 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => r2_hidden(k2_mcart_1(B),k11_relat_1(A,k1_mcart_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_mcart_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13,plain,(
    ! [A_7,B_8] :
      ( k4_tarski(k1_mcart_1(A_7),k2_mcart_1(A_7)) = A_7
      | ~ r2_hidden(A_7,B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15,plain,
    ( k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_13])).

tff(c_18,plain,(
    k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_15])).

tff(c_23,plain,(
    ! [B_9,C_10,A_11] :
      ( r2_hidden(B_9,k11_relat_1(C_10,A_11))
      | ~ r2_hidden(k4_tarski(A_11,B_9),C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [C_15] :
      ( r2_hidden(k2_mcart_1('#skF_2'),k11_relat_1(C_15,k1_mcart_1('#skF_2')))
      | ~ r2_hidden('#skF_2',C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_23])).

tff(c_8,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_2'),k11_relat_1('#skF_1',k1_mcart_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  %$ r2_hidden > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_1
% 1.62/1.08  
% 1.62/1.08  %Foreground sorts:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Background operators:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Foreground operators:
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.62/1.08  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.62/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.08  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.62/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.08  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.62/1.08  
% 1.62/1.09  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => r2_hidden(k2_mcart_1(B), k11_relat_1(A, k1_mcart_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_mcart_1)).
% 1.62/1.09  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.62/1.09  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 1.62/1.09  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.09  tff(c_10, plain, (r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.09  tff(c_13, plain, (![A_7, B_8]: (k4_tarski(k1_mcart_1(A_7), k2_mcart_1(A_7))=A_7 | ~r2_hidden(A_7, B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.09  tff(c_15, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_13])).
% 1.62/1.09  tff(c_18, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_15])).
% 1.62/1.09  tff(c_23, plain, (![B_9, C_10, A_11]: (r2_hidden(B_9, k11_relat_1(C_10, A_11)) | ~r2_hidden(k4_tarski(A_11, B_9), C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.09  tff(c_38, plain, (![C_15]: (r2_hidden(k2_mcart_1('#skF_2'), k11_relat_1(C_15, k1_mcart_1('#skF_2'))) | ~r2_hidden('#skF_2', C_15) | ~v1_relat_1(C_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_23])).
% 1.62/1.09  tff(c_8, plain, (~r2_hidden(k2_mcart_1('#skF_2'), k11_relat_1('#skF_1', k1_mcart_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.09  tff(c_43, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_8])).
% 1.62/1.09  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_43])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 9
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 3
% 1.62/1.09  #Tautology    : 3
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.10  Preprocessing        : 0.26
% 1.62/1.10  Parsing              : 0.15
% 1.62/1.10  CNF conversion       : 0.02
% 1.62/1.10  Main loop            : 0.09
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.02
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.36
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
