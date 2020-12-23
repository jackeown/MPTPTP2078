%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  33 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_tarski(k3_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,k3_tarski(B_24)) = k3_tarski(B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(k3_tarski(B_27),C_26)
      | ~ r2_hidden(A_25,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_126,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_2')
      | ~ r2_hidden(A_28,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_129,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.21  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.75/1.21  
% 1.75/1.21  %Foreground sorts:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Background operators:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Foreground operators:
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.21  
% 1.75/1.22  tff(f_44, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.75/1.22  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.75/1.22  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.75/1.22  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.75/1.22  tff(c_8, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.22  tff(c_10, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.22  tff(c_12, plain, (r1_tarski(k3_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.75/1.22  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.22  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.22  tff(c_87, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_tarski(B_24))=k3_tarski(B_24) | ~r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_6, c_14])).
% 1.75/1.22  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.22  tff(c_112, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(k3_tarski(B_27), C_26) | ~r2_hidden(A_25, B_27))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 1.75/1.22  tff(c_126, plain, (![A_28]: (r1_tarski(A_28, '#skF_2') | ~r2_hidden(A_28, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_112])).
% 1.75/1.22  tff(c_129, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_126])).
% 1.75/1.22  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_129])).
% 1.75/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.22  
% 1.75/1.22  Inference rules
% 1.75/1.22  ----------------------
% 1.75/1.22  #Ref     : 0
% 1.75/1.22  #Sup     : 30
% 1.75/1.22  #Fact    : 0
% 1.75/1.22  #Define  : 0
% 1.75/1.22  #Split   : 0
% 1.75/1.22  #Chain   : 0
% 1.75/1.22  #Close   : 0
% 1.75/1.22  
% 1.75/1.22  Ordering : KBO
% 1.75/1.22  
% 1.75/1.22  Simplification rules
% 1.75/1.22  ----------------------
% 1.75/1.22  #Subsume      : 2
% 1.75/1.22  #Demod        : 1
% 1.75/1.22  #Tautology    : 11
% 1.75/1.22  #SimpNegUnit  : 1
% 1.75/1.22  #BackRed      : 0
% 1.75/1.22  
% 1.75/1.22  #Partial instantiations: 0
% 1.75/1.22  #Strategies tried      : 1
% 1.75/1.22  
% 1.75/1.22  Timing (in seconds)
% 1.75/1.22  ----------------------
% 1.75/1.22  Preprocessing        : 0.24
% 1.75/1.22  Parsing              : 0.14
% 1.75/1.22  CNF conversion       : 0.01
% 1.75/1.22  Main loop            : 0.13
% 1.75/1.22  Inferencing          : 0.06
% 1.75/1.22  Reduction            : 0.03
% 1.75/1.22  Demodulation         : 0.02
% 1.75/1.22  BG Simplification    : 0.01
% 1.75/1.22  Subsumption          : 0.03
% 1.75/1.22  Abstraction          : 0.01
% 1.75/1.22  MUC search           : 0.00
% 1.75/1.22  Cooper               : 0.00
% 1.75/1.22  Total                : 0.40
% 1.75/1.22  Index Insertion      : 0.00
% 1.75/1.22  Index Deletion       : 0.00
% 1.75/1.22  Index Matching       : 0.00
% 1.75/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
