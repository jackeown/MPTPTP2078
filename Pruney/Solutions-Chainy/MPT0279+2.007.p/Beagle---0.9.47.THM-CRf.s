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
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  25 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_51,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),A_23)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_23] : r1_tarski(A_23,A_23) ),
    inference(resolution,[status(thm)],[c_51,c_4])).

tff(c_30,plain,(
    ! [C_15,A_16] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_15,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_25,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    ~ r2_hidden('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_25,c_24])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_29])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.07  
% 1.47/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.08  %$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.47/1.08  
% 1.47/1.08  %Foreground sorts:
% 1.47/1.08  
% 1.47/1.08  
% 1.47/1.08  %Background operators:
% 1.47/1.08  
% 1.47/1.08  
% 1.47/1.08  %Foreground operators:
% 1.47/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.47/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.47/1.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.47/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.47/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.47/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.47/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.47/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.47/1.08  
% 1.63/1.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.09  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.63/1.09  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.63/1.09  tff(f_46, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.63/1.09  tff(c_51, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), A_23) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.09  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.09  tff(c_60, plain, (![A_23]: (r1_tarski(A_23, A_23))), inference(resolution, [status(thm)], [c_51, c_4])).
% 1.63/1.09  tff(c_30, plain, (![C_15, A_16]: (r2_hidden(C_15, k1_zfmisc_1(A_16)) | ~r1_tarski(C_15, A_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.09  tff(c_25, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.09  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.09  tff(c_29, plain, (~r2_hidden('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_25, c_24])).
% 1.63/1.09  tff(c_34, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_29])).
% 1.63/1.09  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_34])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 9
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 0
% 1.63/1.09  #Chain   : 0
% 1.63/1.09  #Close   : 0
% 1.63/1.09  
% 1.63/1.09  Ordering : KBO
% 1.63/1.09  
% 1.63/1.09  Simplification rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Subsume      : 0
% 1.63/1.09  #Demod        : 1
% 1.63/1.09  #Tautology    : 2
% 1.63/1.09  #SimpNegUnit  : 0
% 1.63/1.09  #BackRed      : 1
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.25
% 1.63/1.09  Parsing              : 0.13
% 1.63/1.09  CNF conversion       : 0.02
% 1.63/1.09  Main loop            : 0.09
% 1.63/1.09  Inferencing          : 0.04
% 1.63/1.09  Reduction            : 0.02
% 1.63/1.09  Demodulation         : 0.01
% 1.63/1.09  BG Simplification    : 0.01
% 1.63/1.09  Subsumption          : 0.02
% 1.63/1.10  Abstraction          : 0.00
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.37
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
