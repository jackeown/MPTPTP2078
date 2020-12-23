%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:42 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  51 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    ! [A_100,C_101,B_102] :
      ( r1_tarski(A_100,k2_xboole_0(C_101,B_102))
      | ~ r1_tarski(A_100,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_245,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_307,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_300,c_245])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_326,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_333,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_10])).

tff(c_18,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_204,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,C_77)
      | ~ r1_tarski(k2_tarski(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_211,plain,(
    ! [A_26,C_77] :
      ( r2_hidden(A_26,C_77)
      | ~ r1_tarski(k1_tarski(A_26),C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_204])).

tff(c_339,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_333,c_211])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:17:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.44  
% 2.35/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.44  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.35/1.44  
% 2.35/1.44  %Foreground sorts:
% 2.35/1.44  
% 2.35/1.44  
% 2.35/1.44  %Background operators:
% 2.35/1.44  
% 2.35/1.44  
% 2.35/1.44  %Foreground operators:
% 2.35/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.35/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.44  
% 2.35/1.45  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.35/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.45  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.35/1.45  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.35/1.45  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.45  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.35/1.45  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.45  tff(c_300, plain, (![A_100, C_101, B_102]: (r1_tarski(A_100, k2_xboole_0(C_101, B_102)) | ~r1_tarski(A_100, B_102))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.45  tff(c_42, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.35/1.45  tff(c_101, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.45  tff(c_111, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_101])).
% 2.35/1.45  tff(c_245, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_111])).
% 2.35/1.45  tff(c_307, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_300, c_245])).
% 2.35/1.45  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 2.35/1.45  tff(c_326, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_111])).
% 2.35/1.45  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.45  tff(c_333, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_326, c_10])).
% 2.35/1.45  tff(c_18, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.45  tff(c_204, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, C_77) | ~r1_tarski(k2_tarski(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.35/1.45  tff(c_211, plain, (![A_26, C_77]: (r2_hidden(A_26, C_77) | ~r1_tarski(k1_tarski(A_26), C_77))), inference(superposition, [status(thm), theory('equality')], [c_18, c_204])).
% 2.35/1.45  tff(c_339, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_333, c_211])).
% 2.35/1.45  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_339])).
% 2.35/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.45  
% 2.35/1.45  Inference rules
% 2.35/1.45  ----------------------
% 2.35/1.45  #Ref     : 0
% 2.35/1.45  #Sup     : 67
% 2.35/1.45  #Fact    : 0
% 2.35/1.45  #Define  : 0
% 2.35/1.45  #Split   : 1
% 2.35/1.45  #Chain   : 0
% 2.35/1.45  #Close   : 0
% 2.35/1.45  
% 2.35/1.45  Ordering : KBO
% 2.35/1.45  
% 2.35/1.45  Simplification rules
% 2.35/1.45  ----------------------
% 2.35/1.45  #Subsume      : 1
% 2.35/1.45  #Demod        : 23
% 2.35/1.45  #Tautology    : 41
% 2.35/1.45  #SimpNegUnit  : 1
% 2.35/1.45  #BackRed      : 1
% 2.35/1.45  
% 2.35/1.45  #Partial instantiations: 0
% 2.35/1.45  #Strategies tried      : 1
% 2.35/1.45  
% 2.35/1.45  Timing (in seconds)
% 2.35/1.45  ----------------------
% 2.42/1.45  Preprocessing        : 0.39
% 2.42/1.45  Parsing              : 0.22
% 2.42/1.45  CNF conversion       : 0.02
% 2.42/1.45  Main loop            : 0.19
% 2.42/1.45  Inferencing          : 0.07
% 2.42/1.45  Reduction            : 0.07
% 2.42/1.45  Demodulation         : 0.05
% 2.42/1.45  BG Simplification    : 0.02
% 2.42/1.45  Subsumption          : 0.03
% 2.42/1.45  Abstraction          : 0.01
% 2.42/1.45  MUC search           : 0.00
% 2.42/1.45  Cooper               : 0.00
% 2.42/1.45  Total                : 0.61
% 2.42/1.45  Index Insertion      : 0.00
% 2.42/1.45  Index Deletion       : 0.00
% 2.42/1.45  Index Matching       : 0.00
% 2.42/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
