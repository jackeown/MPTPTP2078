%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:13 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(A_31,C_32)
      | ~ r1_tarski(k2_tarski(A_31,B_33),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,(
    ! [A_31,B_33,B_7] : r2_hidden(A_31,k2_xboole_0(k2_tarski(A_31,B_33),B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_76,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_48,B_49,B_50,B_51] :
      ( r2_hidden(A_48,B_49)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(A_48,B_50),B_51),B_49) ) ),
    inference(resolution,[status(thm)],[c_61,c_76])).

tff(c_108,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n020.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 20:09:07 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  
% 1.69/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.69/1.09  
% 1.69/1.09  %Foreground sorts:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Background operators:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Foreground operators:
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.69/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.69/1.09  
% 1.69/1.09  tff(f_49, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.69/1.09  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.69/1.09  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.69/1.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.69/1.09  tff(c_20, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.09  tff(c_22, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.09  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.69/1.09  tff(c_56, plain, (![A_31, C_32, B_33]: (r2_hidden(A_31, C_32) | ~r1_tarski(k2_tarski(A_31, B_33), C_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.09  tff(c_61, plain, (![A_31, B_33, B_7]: (r2_hidden(A_31, k2_xboole_0(k2_tarski(A_31, B_33), B_7)))), inference(resolution, [status(thm)], [c_8, c_56])).
% 1.69/1.09  tff(c_76, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.09  tff(c_101, plain, (![A_48, B_49, B_50, B_51]: (r2_hidden(A_48, B_49) | ~r1_tarski(k2_xboole_0(k2_tarski(A_48, B_50), B_51), B_49))), inference(resolution, [status(thm)], [c_61, c_76])).
% 1.69/1.09  tff(c_108, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_101])).
% 1.69/1.09  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_108])).
% 1.69/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  
% 1.69/1.09  Inference rules
% 1.69/1.09  ----------------------
% 1.69/1.09  #Ref     : 0
% 1.69/1.09  #Sup     : 19
% 1.69/1.09  #Fact    : 0
% 1.69/1.09  #Define  : 0
% 1.69/1.09  #Split   : 0
% 1.69/1.09  #Chain   : 0
% 1.69/1.09  #Close   : 0
% 1.69/1.09  
% 1.69/1.09  Ordering : KBO
% 1.69/1.09  
% 1.69/1.09  Simplification rules
% 1.69/1.09  ----------------------
% 1.69/1.09  #Subsume      : 2
% 1.69/1.09  #Demod        : 1
% 1.69/1.09  #Tautology    : 7
% 1.69/1.09  #SimpNegUnit  : 1
% 1.69/1.09  #BackRed      : 0
% 1.69/1.09  
% 1.69/1.09  #Partial instantiations: 0
% 1.69/1.09  #Strategies tried      : 1
% 1.69/1.09  
% 1.69/1.09  Timing (in seconds)
% 1.69/1.09  ----------------------
% 1.69/1.10  Preprocessing        : 0.27
% 1.69/1.10  Parsing              : 0.14
% 1.69/1.10  CNF conversion       : 0.02
% 1.69/1.10  Main loop            : 0.12
% 1.69/1.10  Inferencing          : 0.05
% 1.69/1.10  Reduction            : 0.03
% 1.69/1.10  Demodulation         : 0.03
% 1.69/1.10  BG Simplification    : 0.01
% 1.69/1.10  Subsumption          : 0.02
% 1.69/1.10  Abstraction          : 0.01
% 1.69/1.10  MUC search           : 0.00
% 1.69/1.10  Cooper               : 0.00
% 1.69/1.10  Total                : 0.40
% 1.69/1.10  Index Insertion      : 0.00
% 1.69/1.10  Index Deletion       : 0.00
% 1.69/1.10  Index Matching       : 0.00
% 1.69/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
