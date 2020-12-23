%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_27,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27,c_12])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_226,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_xboole_0 = A_37
      | ~ r1_xboole_0(B_38,C_39)
      | ~ r1_tarski(A_37,C_39)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_230,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,'#skF_3')
      | ~ r1_tarski(A_40,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_226])).

tff(c_277,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_43,B_44),'#skF_1')
      | ~ r1_tarski(A_43,k2_xboole_0(B_44,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_230])).

tff(c_322,plain,(
    ! [B_46] :
      ( k4_xboole_0('#skF_1',B_46) = k1_xboole_0
      | ~ r1_tarski('#skF_1',k2_xboole_0(B_46,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_328,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_322])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.29  
% 2.00/1.29  %Foreground sorts:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Background operators:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Foreground operators:
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.29  
% 2.00/1.29  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.00/1.29  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.00/1.29  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.00/1.29  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.00/1.29  tff(f_43, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.00/1.29  tff(c_27, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.29  tff(c_12, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.29  tff(c_35, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_27, c_12])).
% 2.00/1.29  tff(c_16, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.29  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.29  tff(c_8, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.29  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.29  tff(c_226, plain, (![A_37, B_38, C_39]: (k1_xboole_0=A_37 | ~r1_xboole_0(B_38, C_39) | ~r1_tarski(A_37, C_39) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.29  tff(c_230, plain, (![A_40]: (k1_xboole_0=A_40 | ~r1_tarski(A_40, '#skF_3') | ~r1_tarski(A_40, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_226])).
% 2.00/1.29  tff(c_277, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_43, B_44), '#skF_1') | ~r1_tarski(A_43, k2_xboole_0(B_44, '#skF_3')))), inference(resolution, [status(thm)], [c_8, c_230])).
% 2.00/1.29  tff(c_322, plain, (![B_46]: (k4_xboole_0('#skF_1', B_46)=k1_xboole_0 | ~r1_tarski('#skF_1', k2_xboole_0(B_46, '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_277])).
% 2.00/1.29  tff(c_328, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_322])).
% 2.00/1.29  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_328])).
% 2.00/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  Inference rules
% 2.00/1.29  ----------------------
% 2.00/1.29  #Ref     : 0
% 2.00/1.29  #Sup     : 82
% 2.00/1.29  #Fact    : 0
% 2.00/1.29  #Define  : 0
% 2.00/1.29  #Split   : 0
% 2.00/1.29  #Chain   : 0
% 2.00/1.29  #Close   : 0
% 2.00/1.29  
% 2.00/1.29  Ordering : KBO
% 2.00/1.29  
% 2.00/1.29  Simplification rules
% 2.00/1.29  ----------------------
% 2.00/1.29  #Subsume      : 9
% 2.00/1.29  #Demod        : 29
% 2.00/1.29  #Tautology    : 36
% 2.00/1.29  #SimpNegUnit  : 1
% 2.00/1.29  #BackRed      : 0
% 2.00/1.29  
% 2.00/1.29  #Partial instantiations: 0
% 2.00/1.29  #Strategies tried      : 1
% 2.00/1.29  
% 2.00/1.29  Timing (in seconds)
% 2.00/1.29  ----------------------
% 2.00/1.30  Preprocessing        : 0.27
% 2.00/1.30  Parsing              : 0.15
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.22
% 2.00/1.30  Inferencing          : 0.09
% 2.00/1.30  Reduction            : 0.06
% 2.00/1.30  Demodulation         : 0.05
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.05
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.51
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
