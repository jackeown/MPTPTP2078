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
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   34 (  52 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  98 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [A_22,B_23] :
      ( k4_tarski(k1_mcart_1(A_22),k2_mcart_1(A_22)) = A_22
      | ~ r2_hidden(A_22,B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,
    ( k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_55,plain,(
    k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] :
      ( r2_hidden(B_2,k2_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [C_24] :
      ( r2_hidden(k2_mcart_1('#skF_2'),k2_relat_1(C_24))
      | ~ r2_hidden('#skF_2',C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_tarski(k1_mcart_1(A_13),k2_mcart_1(A_13)) = A_13
      | ~ r2_hidden(A_13,B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,
    ( k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_21,plain,(
    k4_tarski(k1_mcart_1('#skF_2'),k2_mcart_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k1_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [C_15] :
      ( r2_hidden(k1_mcart_1('#skF_2'),k1_relat_1(C_15))
      | ~ r2_hidden('#skF_2',C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_4])).

tff(c_8,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_2'),k2_relat_1('#skF_1'))
    | ~ r2_hidden(k1_mcart_1('#skF_2'),k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_2'),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_37,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_13])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_37])).

tff(c_43,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_2'),k2_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_67,c_43])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.16  
% 1.58/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.16  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_2 > #skF_1
% 1.58/1.16  
% 1.58/1.16  %Foreground sorts:
% 1.58/1.16  
% 1.58/1.16  
% 1.58/1.16  %Background operators:
% 1.58/1.16  
% 1.58/1.16  
% 1.58/1.16  %Foreground operators:
% 1.58/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.58/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.58/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.58/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.58/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.58/1.16  
% 1.58/1.17  tff(f_49, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 1.58/1.17  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.58/1.17  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.58/1.17  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.17  tff(c_10, plain, (r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.17  tff(c_47, plain, (![A_22, B_23]: (k4_tarski(k1_mcart_1(A_22), k2_mcart_1(A_22))=A_22 | ~r2_hidden(A_22, B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.17  tff(c_51, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_47])).
% 1.58/1.17  tff(c_55, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_51])).
% 1.58/1.17  tff(c_2, plain, (![B_2, C_3, A_1]: (r2_hidden(B_2, k2_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.17  tff(c_67, plain, (![C_24]: (r2_hidden(k2_mcart_1('#skF_2'), k2_relat_1(C_24)) | ~r2_hidden('#skF_2', C_24) | ~v1_relat_1(C_24))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 1.58/1.17  tff(c_16, plain, (![A_13, B_14]: (k4_tarski(k1_mcart_1(A_13), k2_mcart_1(A_13))=A_13 | ~r2_hidden(A_13, B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.17  tff(c_18, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.58/1.17  tff(c_21, plain, (k4_tarski(k1_mcart_1('#skF_2'), k2_mcart_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 1.58/1.17  tff(c_4, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k1_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.17  tff(c_32, plain, (![C_15]: (r2_hidden(k1_mcart_1('#skF_2'), k1_relat_1(C_15)) | ~r2_hidden('#skF_2', C_15) | ~v1_relat_1(C_15))), inference(superposition, [status(thm), theory('equality')], [c_21, c_4])).
% 1.58/1.17  tff(c_8, plain, (~r2_hidden(k2_mcart_1('#skF_2'), k2_relat_1('#skF_1')) | ~r2_hidden(k1_mcart_1('#skF_2'), k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.17  tff(c_13, plain, (~r2_hidden(k1_mcart_1('#skF_2'), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_8])).
% 1.58/1.17  tff(c_37, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_13])).
% 1.58/1.17  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_37])).
% 1.58/1.17  tff(c_43, plain, (~r2_hidden(k2_mcart_1('#skF_2'), k2_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_8])).
% 1.58/1.17  tff(c_72, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_67, c_43])).
% 1.58/1.17  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_72])).
% 1.58/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.17  
% 1.58/1.17  Inference rules
% 1.58/1.17  ----------------------
% 1.58/1.17  #Ref     : 0
% 1.58/1.17  #Sup     : 15
% 1.58/1.17  #Fact    : 0
% 1.58/1.17  #Define  : 0
% 1.58/1.17  #Split   : 2
% 1.58/1.17  #Chain   : 0
% 1.58/1.17  #Close   : 0
% 1.58/1.17  
% 1.58/1.17  Ordering : KBO
% 1.58/1.17  
% 1.58/1.17  Simplification rules
% 1.58/1.17  ----------------------
% 1.58/1.17  #Subsume      : 0
% 1.58/1.17  #Demod        : 6
% 1.58/1.17  #Tautology    : 4
% 1.58/1.17  #SimpNegUnit  : 0
% 1.58/1.17  #BackRed      : 0
% 1.58/1.17  
% 1.58/1.17  #Partial instantiations: 0
% 1.58/1.17  #Strategies tried      : 1
% 1.58/1.17  
% 1.58/1.17  Timing (in seconds)
% 1.58/1.17  ----------------------
% 1.58/1.17  Preprocessing        : 0.27
% 1.58/1.17  Parsing              : 0.15
% 1.58/1.17  CNF conversion       : 0.02
% 1.58/1.17  Main loop            : 0.11
% 1.58/1.17  Inferencing          : 0.05
% 1.58/1.17  Reduction            : 0.03
% 1.58/1.17  Demodulation         : 0.02
% 1.58/1.17  BG Simplification    : 0.01
% 1.58/1.17  Subsumption          : 0.01
% 1.58/1.17  Abstraction          : 0.00
% 1.58/1.18  MUC search           : 0.00
% 1.58/1.18  Cooper               : 0.00
% 1.58/1.18  Total                : 0.41
% 1.58/1.18  Index Insertion      : 0.00
% 1.58/1.18  Index Deletion       : 0.00
% 1.58/1.18  Index Matching       : 0.00
% 1.58/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
