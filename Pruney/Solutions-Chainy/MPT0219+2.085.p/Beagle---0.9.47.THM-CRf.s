%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 5.99s
% Output     : CNFRefutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_164,plain,(
    ! [A_82,B_83] : k2_xboole_0(k1_tarski(A_82),k1_tarski(B_83)) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_58])).

tff(c_113,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    ! [B_72,A_71] : r2_hidden(B_72,k2_tarski(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_195,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_119])).

tff(c_42,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_732,plain,(
    ! [E_106,C_107,B_108,A_109] :
      ( E_106 = C_107
      | E_106 = B_108
      | E_106 = A_109
      | ~ r2_hidden(E_106,k1_enumset1(A_109,B_108,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3810,plain,(
    ! [E_199,B_200,A_201] :
      ( E_199 = B_200
      | E_199 = A_201
      | E_199 = A_201
      | ~ r2_hidden(E_199,k2_tarski(A_201,B_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_732])).

tff(c_3872,plain,(
    ! [E_203,A_204] :
      ( E_203 = A_204
      | E_203 = A_204
      | E_203 = A_204
      | ~ r2_hidden(E_203,k1_tarski(A_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3810])).

tff(c_3883,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_195,c_3872])).

tff(c_3892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_56,c_3883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.99/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.28  
% 5.99/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.28  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.99/2.28  
% 5.99/2.28  %Foreground sorts:
% 5.99/2.28  
% 5.99/2.28  
% 5.99/2.28  %Background operators:
% 5.99/2.28  
% 5.99/2.28  
% 5.99/2.28  %Foreground operators:
% 5.99/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.99/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.99/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.99/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.99/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.99/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.99/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.99/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.99/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.99/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.99/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.99/2.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.99/2.28  tff('#skF_4', type, '#skF_4': $i).
% 5.99/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.99/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.99/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.99/2.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.99/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.99/2.28  
% 5.99/2.29  tff(f_75, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 5.99/2.29  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.99/2.29  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.99/2.29  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.99/2.29  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.99/2.29  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.29  tff(c_164, plain, (![A_82, B_83]: (k2_xboole_0(k1_tarski(A_82), k1_tarski(B_83))=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.99/2.29  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.99/2.29  tff(c_170, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_164, c_58])).
% 5.99/2.29  tff(c_113, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.99/2.29  tff(c_16, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.99/2.29  tff(c_119, plain, (![B_72, A_71]: (r2_hidden(B_72, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 5.99/2.29  tff(c_195, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_119])).
% 5.99/2.29  tff(c_42, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.99/2.29  tff(c_44, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.99/2.29  tff(c_732, plain, (![E_106, C_107, B_108, A_109]: (E_106=C_107 | E_106=B_108 | E_106=A_109 | ~r2_hidden(E_106, k1_enumset1(A_109, B_108, C_107)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.99/2.29  tff(c_3810, plain, (![E_199, B_200, A_201]: (E_199=B_200 | E_199=A_201 | E_199=A_201 | ~r2_hidden(E_199, k2_tarski(A_201, B_200)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_732])).
% 5.99/2.29  tff(c_3872, plain, (![E_203, A_204]: (E_203=A_204 | E_203=A_204 | E_203=A_204 | ~r2_hidden(E_203, k1_tarski(A_204)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3810])).
% 5.99/2.29  tff(c_3883, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_195, c_3872])).
% 5.99/2.29  tff(c_3892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_56, c_3883])).
% 5.99/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.99/2.29  
% 5.99/2.29  Inference rules
% 5.99/2.29  ----------------------
% 5.99/2.29  #Ref     : 0
% 5.99/2.29  #Sup     : 1010
% 5.99/2.29  #Fact    : 0
% 5.99/2.29  #Define  : 0
% 5.99/2.29  #Split   : 0
% 5.99/2.29  #Chain   : 0
% 5.99/2.29  #Close   : 0
% 5.99/2.29  
% 5.99/2.29  Ordering : KBO
% 5.99/2.29  
% 5.99/2.29  Simplification rules
% 5.99/2.29  ----------------------
% 5.99/2.29  #Subsume      : 118
% 5.99/2.29  #Demod        : 602
% 5.99/2.29  #Tautology    : 260
% 5.99/2.29  #SimpNegUnit  : 3
% 5.99/2.29  #BackRed      : 0
% 5.99/2.29  
% 5.99/2.29  #Partial instantiations: 0
% 5.99/2.29  #Strategies tried      : 1
% 5.99/2.29  
% 5.99/2.29  Timing (in seconds)
% 5.99/2.29  ----------------------
% 5.99/2.30  Preprocessing        : 0.34
% 5.99/2.30  Parsing              : 0.18
% 5.99/2.30  CNF conversion       : 0.02
% 5.99/2.30  Main loop            : 1.14
% 5.99/2.30  Inferencing          : 0.26
% 5.99/2.30  Reduction            : 0.67
% 5.99/2.30  Demodulation         : 0.61
% 5.99/2.30  BG Simplification    : 0.05
% 5.99/2.30  Subsumption          : 0.12
% 5.99/2.30  Abstraction          : 0.06
% 5.99/2.30  MUC search           : 0.00
% 5.99/2.30  Cooper               : 0.00
% 5.99/2.30  Total                : 1.50
% 5.99/2.30  Index Insertion      : 0.00
% 5.99/2.30  Index Deletion       : 0.00
% 5.99/2.30  Index Matching       : 0.00
% 5.99/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
