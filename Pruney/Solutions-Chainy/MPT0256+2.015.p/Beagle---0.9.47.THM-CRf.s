%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [D_27,A_28,B_29] :
      ( r2_hidden(D_27,A_28)
      | ~ r2_hidden(D_27,k3_xboole_0(A_28,B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_6])).

tff(c_86,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_5')
      | ~ r2_hidden(D_30,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_82])).

tff(c_90,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.70/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.12  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.70/1.12  
% 1.70/1.13  tff(f_51, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.70/1.13  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.70/1.13  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.70/1.13  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.70/1.13  tff(c_36, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.13  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.70/1.13  tff(c_38, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.13  tff(c_60, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.13  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.13  tff(c_82, plain, (![D_27, A_28, B_29]: (r2_hidden(D_27, A_28) | ~r2_hidden(D_27, k3_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_6])).
% 1.70/1.13  tff(c_86, plain, (![D_30]: (r2_hidden(D_30, '#skF_5') | ~r2_hidden(D_30, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_82])).
% 1.70/1.13  tff(c_90, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_86])).
% 1.70/1.13  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_90])).
% 1.70/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.13  
% 1.70/1.13  Inference rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Ref     : 0
% 1.70/1.13  #Sup     : 13
% 1.70/1.13  #Fact    : 0
% 1.70/1.13  #Define  : 0
% 1.70/1.13  #Split   : 0
% 1.70/1.13  #Chain   : 0
% 1.70/1.13  #Close   : 0
% 1.70/1.13  
% 1.70/1.13  Ordering : KBO
% 1.70/1.13  
% 1.70/1.13  Simplification rules
% 1.70/1.13  ----------------------
% 1.70/1.13  #Subsume      : 0
% 1.70/1.13  #Demod        : 0
% 1.70/1.13  #Tautology    : 7
% 1.70/1.13  #SimpNegUnit  : 1
% 1.70/1.13  #BackRed      : 0
% 1.70/1.13  
% 1.70/1.13  #Partial instantiations: 0
% 1.70/1.13  #Strategies tried      : 1
% 1.70/1.13  
% 1.70/1.13  Timing (in seconds)
% 1.70/1.13  ----------------------
% 1.70/1.13  Preprocessing        : 0.29
% 1.70/1.13  Parsing              : 0.15
% 1.70/1.13  CNF conversion       : 0.02
% 1.70/1.13  Main loop            : 0.09
% 1.70/1.13  Inferencing          : 0.03
% 1.70/1.13  Reduction            : 0.03
% 1.70/1.13  Demodulation         : 0.02
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.02
% 1.70/1.13  Abstraction          : 0.01
% 1.70/1.14  MUC search           : 0.00
% 1.70/1.14  Cooper               : 0.00
% 1.70/1.14  Total                : 0.40
% 1.70/1.14  Index Insertion      : 0.00
% 1.70/1.14  Index Deletion       : 0.00
% 1.70/1.14  Index Matching       : 0.00
% 1.70/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
