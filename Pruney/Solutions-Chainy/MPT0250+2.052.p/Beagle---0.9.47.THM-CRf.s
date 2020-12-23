%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,k2_xboole_0(C_9,B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_260,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_263])).

tff(c_268,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_20,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [B_76,C_77,A_78] :
      ( r2_hidden(B_76,C_77)
      | ~ r1_tarski(k2_tarski(A_78,B_76),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_286,plain,(
    ! [B_84,A_85,B_86] : r2_hidden(B_84,k2_xboole_0(k2_tarski(A_85,B_84),B_86)) ),
    inference(resolution,[status(thm)],[c_14,c_226])).

tff(c_303,plain,(
    ! [A_90,B_91] : r2_hidden(A_90,k2_xboole_0(k1_tarski(A_90),B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_286])).

tff(c_306,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_303])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.44  
% 2.30/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.44  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.30/1.44  
% 2.30/1.44  %Foreground sorts:
% 2.30/1.44  
% 2.30/1.44  
% 2.30/1.44  %Background operators:
% 2.30/1.44  
% 2.30/1.44  
% 2.30/1.44  %Foreground operators:
% 2.30/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.30/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.44  
% 2.30/1.45  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.30/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.45  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.30/1.45  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.30/1.45  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.30/1.45  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.30/1.45  tff(c_44, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.45  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.45  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, k2_xboole_0(C_9, B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.45  tff(c_46, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.30/1.45  tff(c_176, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.45  tff(c_189, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_176])).
% 2.30/1.45  tff(c_260, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_189])).
% 2.30/1.45  tff(c_263, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_12, c_260])).
% 2.30/1.45  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_263])).
% 2.30/1.45  tff(c_268, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_189])).
% 2.30/1.45  tff(c_20, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.45  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.45  tff(c_226, plain, (![B_76, C_77, A_78]: (r2_hidden(B_76, C_77) | ~r1_tarski(k2_tarski(A_78, B_76), C_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.30/1.45  tff(c_286, plain, (![B_84, A_85, B_86]: (r2_hidden(B_84, k2_xboole_0(k2_tarski(A_85, B_84), B_86)))), inference(resolution, [status(thm)], [c_14, c_226])).
% 2.30/1.45  tff(c_303, plain, (![A_90, B_91]: (r2_hidden(A_90, k2_xboole_0(k1_tarski(A_90), B_91)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_286])).
% 2.30/1.45  tff(c_306, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_268, c_303])).
% 2.30/1.45  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_306])).
% 2.30/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.45  
% 2.30/1.45  Inference rules
% 2.30/1.45  ----------------------
% 2.30/1.45  #Ref     : 0
% 2.30/1.45  #Sup     : 61
% 2.30/1.45  #Fact    : 0
% 2.30/1.45  #Define  : 0
% 2.30/1.45  #Split   : 1
% 2.30/1.45  #Chain   : 0
% 2.30/1.45  #Close   : 0
% 2.30/1.45  
% 2.30/1.45  Ordering : KBO
% 2.30/1.45  
% 2.30/1.45  Simplification rules
% 2.30/1.45  ----------------------
% 2.30/1.45  #Subsume      : 0
% 2.30/1.45  #Demod        : 10
% 2.30/1.45  #Tautology    : 38
% 2.30/1.45  #SimpNegUnit  : 1
% 2.30/1.45  #BackRed      : 1
% 2.30/1.45  
% 2.30/1.45  #Partial instantiations: 0
% 2.30/1.45  #Strategies tried      : 1
% 2.30/1.45  
% 2.30/1.45  Timing (in seconds)
% 2.30/1.45  ----------------------
% 2.50/1.45  Preprocessing        : 0.44
% 2.50/1.45  Parsing              : 0.25
% 2.50/1.45  CNF conversion       : 0.02
% 2.50/1.45  Main loop            : 0.19
% 2.50/1.45  Inferencing          : 0.06
% 2.50/1.45  Reduction            : 0.07
% 2.50/1.45  Demodulation         : 0.05
% 2.50/1.45  BG Simplification    : 0.02
% 2.50/1.45  Subsumption          : 0.04
% 2.50/1.45  Abstraction          : 0.02
% 2.50/1.45  MUC search           : 0.00
% 2.50/1.45  Cooper               : 0.00
% 2.50/1.45  Total                : 0.66
% 2.50/1.45  Index Insertion      : 0.00
% 2.50/1.45  Index Deletion       : 0.00
% 2.50/1.45  Index Matching       : 0.00
% 2.50/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
