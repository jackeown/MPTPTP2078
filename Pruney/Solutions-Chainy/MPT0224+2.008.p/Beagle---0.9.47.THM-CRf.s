%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:30 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_82,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_71,A_72] :
      ( k1_tarski(B_71) = A_72
      | k1_xboole_0 = A_72
      | ~ r1_tarski(A_72,k1_tarski(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,(
    ! [B_82,B_83] :
      ( k3_xboole_0(k1_tarski(B_82),B_83) = k1_tarski(B_82)
      | k3_xboole_0(k1_tarski(B_82),B_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_54,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_54])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,B_61)
      | ~ r1_xboole_0(k1_tarski(A_60),B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ! [A_60,B_2] :
      ( ~ r2_hidden(A_60,B_2)
      | k3_xboole_0(k1_tarski(A_60),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_177,plain,(
    ~ r2_hidden('#skF_3',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_76])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.26  
% 2.09/1.26  %Foreground sorts:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Background operators:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Foreground operators:
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.09/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.09/1.26  
% 2.09/1.27  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.27  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.27  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.09/1.27  tff(f_71, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.09/1.27  tff(f_74, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.09/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.09/1.27  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.09/1.27  tff(c_82, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.27  tff(c_12, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.27  tff(c_91, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 2.09/1.27  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.27  tff(c_110, plain, (![B_71, A_72]: (k1_tarski(B_71)=A_72 | k1_xboole_0=A_72 | ~r1_tarski(A_72, k1_tarski(B_71)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.27  tff(c_150, plain, (![B_82, B_83]: (k3_xboole_0(k1_tarski(B_82), B_83)=k1_tarski(B_82) | k3_xboole_0(k1_tarski(B_82), B_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.09/1.27  tff(c_54, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.27  tff(c_167, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_150, c_54])).
% 2.09/1.27  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.27  tff(c_71, plain, (![A_60, B_61]: (~r2_hidden(A_60, B_61) | ~r1_xboole_0(k1_tarski(A_60), B_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.09/1.27  tff(c_76, plain, (![A_60, B_2]: (~r2_hidden(A_60, B_2) | k3_xboole_0(k1_tarski(A_60), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.09/1.27  tff(c_177, plain, (~r2_hidden('#skF_3', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_76])).
% 2.09/1.27  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_177])).
% 2.09/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  Inference rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Ref     : 0
% 2.09/1.27  #Sup     : 29
% 2.09/1.27  #Fact    : 1
% 2.09/1.27  #Define  : 0
% 2.09/1.27  #Split   : 0
% 2.09/1.27  #Chain   : 0
% 2.09/1.27  #Close   : 0
% 2.09/1.27  
% 2.09/1.27  Ordering : KBO
% 2.09/1.27  
% 2.09/1.27  Simplification rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Subsume      : 0
% 2.09/1.27  #Demod        : 6
% 2.09/1.27  #Tautology    : 18
% 2.09/1.27  #SimpNegUnit  : 0
% 2.09/1.27  #BackRed      : 1
% 2.09/1.27  
% 2.09/1.27  #Partial instantiations: 0
% 2.09/1.27  #Strategies tried      : 1
% 2.09/1.27  
% 2.09/1.27  Timing (in seconds)
% 2.09/1.27  ----------------------
% 2.09/1.28  Preprocessing        : 0.34
% 2.09/1.28  Parsing              : 0.18
% 2.09/1.28  CNF conversion       : 0.02
% 2.09/1.28  Main loop            : 0.15
% 2.09/1.28  Inferencing          : 0.05
% 2.09/1.28  Reduction            : 0.05
% 2.09/1.28  Demodulation         : 0.04
% 2.09/1.28  BG Simplification    : 0.02
% 2.09/1.28  Subsumption          : 0.03
% 2.09/1.28  Abstraction          : 0.01
% 2.09/1.28  MUC search           : 0.00
% 2.09/1.28  Cooper               : 0.00
% 2.09/1.28  Total                : 0.52
% 2.09/1.28  Index Insertion      : 0.00
% 2.09/1.28  Index Deletion       : 0.00
% 2.09/1.28  Index Matching       : 0.00
% 2.09/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
