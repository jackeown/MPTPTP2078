%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_72,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_254,plain,(
    ! [A_96,B_97] : k2_xboole_0(k1_tarski(A_96),k1_tarski(B_97)) = k2_tarski(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_269,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_74])).

tff(c_185,plain,(
    ! [A_84,B_85] : k1_enumset1(A_84,A_84,B_85) = k2_tarski(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [E_24,A_18,B_19] : r2_hidden(E_24,k1_enumset1(A_18,B_19,E_24)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    ! [B_85,A_84] : r2_hidden(B_85,k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_20])).

tff(c_300,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_197])).

tff(c_42,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_310,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_300,c_42])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  
% 2.21/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.27  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.21/1.27  
% 2.21/1.27  %Foreground sorts:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Background operators:
% 2.21/1.27  
% 2.21/1.27  
% 2.21/1.27  %Foreground operators:
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.21/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.21/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.21/1.27  
% 2.21/1.28  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.21/1.28  tff(f_65, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.21/1.28  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.28  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.21/1.28  tff(f_63, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.21/1.28  tff(c_72, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.28  tff(c_254, plain, (![A_96, B_97]: (k2_xboole_0(k1_tarski(A_96), k1_tarski(B_97))=k2_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.28  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.28  tff(c_269, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_254, c_74])).
% 2.21/1.28  tff(c_185, plain, (![A_84, B_85]: (k1_enumset1(A_84, A_84, B_85)=k2_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.21/1.28  tff(c_20, plain, (![E_24, A_18, B_19]: (r2_hidden(E_24, k1_enumset1(A_18, B_19, E_24)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.28  tff(c_197, plain, (![B_85, A_84]: (r2_hidden(B_85, k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_20])).
% 2.21/1.28  tff(c_300, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_269, c_197])).
% 2.21/1.28  tff(c_42, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.28  tff(c_310, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_300, c_42])).
% 2.21/1.28  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_310])).
% 2.21/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  Inference rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Ref     : 0
% 2.21/1.28  #Sup     : 61
% 2.21/1.28  #Fact    : 0
% 2.21/1.28  #Define  : 0
% 2.21/1.28  #Split   : 0
% 2.21/1.28  #Chain   : 0
% 2.21/1.28  #Close   : 0
% 2.21/1.28  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 0
% 2.21/1.28  #Demod        : 9
% 2.21/1.28  #Tautology    : 46
% 2.21/1.28  #SimpNegUnit  : 1
% 2.21/1.28  #BackRed      : 0
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.29  Preprocessing        : 0.35
% 2.21/1.29  Parsing              : 0.18
% 2.21/1.29  CNF conversion       : 0.03
% 2.21/1.29  Main loop            : 0.18
% 2.21/1.29  Inferencing          : 0.05
% 2.21/1.29  Reduction            : 0.07
% 2.21/1.29  Demodulation         : 0.05
% 2.21/1.29  BG Simplification    : 0.02
% 2.21/1.29  Subsumption          : 0.04
% 2.21/1.29  Abstraction          : 0.01
% 2.21/1.29  MUC search           : 0.00
% 2.21/1.29  Cooper               : 0.00
% 2.21/1.29  Total                : 0.55
% 2.21/1.29  Index Insertion      : 0.00
% 2.21/1.29  Index Deletion       : 0.00
% 2.21/1.29  Index Matching       : 0.00
% 2.21/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
