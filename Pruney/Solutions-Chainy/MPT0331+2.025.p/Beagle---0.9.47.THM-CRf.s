%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:48 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & ~ r1_xboole_0(k2_tarski(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l168_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_xboole_0(k2_tarski(A_18,B_19),C_20)
      | r2_hidden(B_19,C_20)
      | r2_hidden(A_18,C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_xboole_0(C_21,k2_tarski(A_22,B_23))
      | r2_hidden(B_23,C_21)
      | r2_hidden(A_22,C_21) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [C_24,A_25,B_26] :
      ( k4_xboole_0(C_24,k2_tarski(A_25,B_26)) = C_24
      | r2_hidden(B_26,C_24)
      | r2_hidden(A_25,C_24) ) ),
    inference(resolution,[status(thm)],[c_42,c_4])).

tff(c_10,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_12,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.19  
% 1.69/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.19  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.69/1.19  
% 1.69/1.19  %Foreground sorts:
% 1.69/1.19  
% 1.69/1.19  
% 1.69/1.19  %Background operators:
% 1.69/1.19  
% 1.69/1.19  
% 1.69/1.19  %Foreground operators:
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.19  
% 1.69/1.20  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.69/1.20  tff(f_43, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~r1_xboole_0(k2_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l168_zfmisc_1)).
% 1.69/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.69/1.20  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.69/1.20  tff(c_14, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.20  tff(c_12, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.20  tff(c_34, plain, (![A_18, B_19, C_20]: (r1_xboole_0(k2_tarski(A_18, B_19), C_20) | r2_hidden(B_19, C_20) | r2_hidden(A_18, C_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.69/1.20  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.20  tff(c_42, plain, (![C_21, A_22, B_23]: (r1_xboole_0(C_21, k2_tarski(A_22, B_23)) | r2_hidden(B_23, C_21) | r2_hidden(A_22, C_21))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.69/1.20  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.20  tff(c_50, plain, (![C_24, A_25, B_26]: (k4_xboole_0(C_24, k2_tarski(A_25, B_26))=C_24 | r2_hidden(B_26, C_24) | r2_hidden(A_25, C_24))), inference(resolution, [status(thm)], [c_42, c_4])).
% 1.69/1.20  tff(c_10, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.69/1.20  tff(c_58, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_10])).
% 1.69/1.20  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_12, c_58])).
% 1.69/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.20  
% 1.69/1.20  Inference rules
% 1.69/1.20  ----------------------
% 1.69/1.20  #Ref     : 0
% 1.69/1.20  #Sup     : 12
% 1.69/1.20  #Fact    : 0
% 1.69/1.20  #Define  : 0
% 1.69/1.20  #Split   : 0
% 1.69/1.20  #Chain   : 0
% 1.69/1.20  #Close   : 0
% 1.69/1.20  
% 1.69/1.20  Ordering : KBO
% 1.69/1.20  
% 1.69/1.20  Simplification rules
% 1.69/1.20  ----------------------
% 1.69/1.20  #Subsume      : 2
% 1.69/1.20  #Demod        : 0
% 1.69/1.20  #Tautology    : 2
% 1.69/1.20  #SimpNegUnit  : 1
% 1.69/1.20  #BackRed      : 0
% 1.69/1.20  
% 1.69/1.20  #Partial instantiations: 0
% 1.69/1.20  #Strategies tried      : 1
% 1.69/1.20  
% 1.69/1.20  Timing (in seconds)
% 1.69/1.20  ----------------------
% 1.69/1.20  Preprocessing        : 0.26
% 1.69/1.20  Parsing              : 0.14
% 1.69/1.20  CNF conversion       : 0.02
% 1.69/1.20  Main loop            : 0.11
% 1.69/1.20  Inferencing          : 0.06
% 1.69/1.20  Reduction            : 0.02
% 1.69/1.20  Demodulation         : 0.00
% 1.69/1.20  BG Simplification    : 0.01
% 1.69/1.20  Subsumption          : 0.02
% 1.69/1.20  Abstraction          : 0.01
% 1.69/1.20  MUC search           : 0.00
% 1.69/1.20  Cooper               : 0.00
% 1.69/1.20  Total                : 0.40
% 1.69/1.20  Index Insertion      : 0.00
% 1.69/1.20  Index Deletion       : 0.00
% 1.69/1.20  Index Matching       : 0.00
% 1.69/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
