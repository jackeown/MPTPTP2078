%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:50 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_100,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_102,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_131,plain,(
    ! [B_94,A_95] : k2_xboole_0(B_94,A_95) = k2_xboole_0(A_95,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_100,B_101] : r1_tarski(A_100,k2_xboole_0(B_101,A_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_42])).

tff(c_248,plain,(
    r1_tarski(k1_tarski('#skF_9'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_242])).

tff(c_72,plain,(
    ! [C_38] : r2_hidden(C_38,k1_tarski(C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1075,plain,(
    ! [C_159,B_160,A_161] :
      ( r2_hidden(C_159,B_160)
      | ~ r2_hidden(C_159,A_161)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2394,plain,(
    ! [C_3905,B_3906] :
      ( r2_hidden(C_3905,B_3906)
      | ~ r1_tarski(k1_tarski(C_3905),B_3906) ) ),
    inference(resolution,[status(thm)],[c_72,c_1075])).

tff(c_2414,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_248,c_2394])).

tff(c_70,plain,(
    ! [C_38,A_34] :
      ( C_38 = A_34
      | ~ r2_hidden(C_38,k1_tarski(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2423,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2414,c_70])).

tff(c_2471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_2423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.65  
% 3.57/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.65  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 3.57/1.65  
% 3.57/1.65  %Foreground sorts:
% 3.57/1.65  
% 3.57/1.65  
% 3.57/1.65  %Background operators:
% 3.57/1.65  
% 3.57/1.65  
% 3.57/1.65  %Foreground operators:
% 3.57/1.65  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.57/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.57/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.57/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.57/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.57/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.57/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.57/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.57/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.65  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.57/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.65  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.57/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.57/1.65  
% 3.57/1.66  tff(f_109, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.57/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.57/1.66  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.57/1.66  tff(f_86, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.57/1.66  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.57/1.66  tff(c_100, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.57/1.66  tff(c_102, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.57/1.66  tff(c_131, plain, (![B_94, A_95]: (k2_xboole_0(B_94, A_95)=k2_xboole_0(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.66  tff(c_42, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/1.66  tff(c_242, plain, (![A_100, B_101]: (r1_tarski(A_100, k2_xboole_0(B_101, A_100)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_42])).
% 3.57/1.66  tff(c_248, plain, (r1_tarski(k1_tarski('#skF_9'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_242])).
% 3.57/1.66  tff(c_72, plain, (![C_38]: (r2_hidden(C_38, k1_tarski(C_38)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.57/1.66  tff(c_1075, plain, (![C_159, B_160, A_161]: (r2_hidden(C_159, B_160) | ~r2_hidden(C_159, A_161) | ~r1_tarski(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.57/1.66  tff(c_2394, plain, (![C_3905, B_3906]: (r2_hidden(C_3905, B_3906) | ~r1_tarski(k1_tarski(C_3905), B_3906))), inference(resolution, [status(thm)], [c_72, c_1075])).
% 3.57/1.66  tff(c_2414, plain, (r2_hidden('#skF_9', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_248, c_2394])).
% 3.57/1.66  tff(c_70, plain, (![C_38, A_34]: (C_38=A_34 | ~r2_hidden(C_38, k1_tarski(A_34)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.57/1.66  tff(c_2423, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2414, c_70])).
% 3.57/1.66  tff(c_2471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_2423])).
% 3.57/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.66  
% 3.57/1.66  Inference rules
% 3.57/1.66  ----------------------
% 3.57/1.66  #Ref     : 0
% 3.57/1.66  #Sup     : 399
% 3.57/1.66  #Fact    : 0
% 3.57/1.66  #Define  : 0
% 3.57/1.66  #Split   : 3
% 3.57/1.66  #Chain   : 0
% 3.57/1.66  #Close   : 0
% 3.57/1.66  
% 3.57/1.66  Ordering : KBO
% 3.57/1.66  
% 3.57/1.66  Simplification rules
% 3.57/1.66  ----------------------
% 3.57/1.66  #Subsume      : 58
% 3.57/1.66  #Demod        : 153
% 3.57/1.66  #Tautology    : 221
% 3.57/1.66  #SimpNegUnit  : 7
% 3.57/1.66  #BackRed      : 5
% 3.57/1.66  
% 3.57/1.66  #Partial instantiations: 1298
% 3.57/1.66  #Strategies tried      : 1
% 3.57/1.66  
% 3.57/1.66  Timing (in seconds)
% 3.57/1.66  ----------------------
% 3.57/1.66  Preprocessing        : 0.36
% 3.57/1.66  Parsing              : 0.19
% 3.57/1.66  CNF conversion       : 0.03
% 3.57/1.66  Main loop            : 0.49
% 3.57/1.66  Inferencing          : 0.21
% 3.57/1.66  Reduction            : 0.16
% 3.57/1.66  Demodulation         : 0.12
% 3.57/1.66  BG Simplification    : 0.03
% 3.57/1.66  Subsumption          : 0.08
% 3.57/1.66  Abstraction          : 0.02
% 3.57/1.66  MUC search           : 0.00
% 3.57/1.66  Cooper               : 0.00
% 3.57/1.66  Total                : 0.88
% 3.57/1.66  Index Insertion      : 0.00
% 3.57/1.66  Index Deletion       : 0.00
% 3.57/1.66  Index Matching       : 0.00
% 3.57/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
