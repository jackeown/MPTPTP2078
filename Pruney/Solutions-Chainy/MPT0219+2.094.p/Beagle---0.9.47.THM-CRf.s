%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  44 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    ! [A_29,B_30] : k2_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_309,plain,(
    ! [A_108,B_109] : k2_xboole_0(k1_tarski(A_108),k1_tarski(B_109)) = k2_tarski(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_315,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_62])).

tff(c_398,plain,(
    ! [A_116,B_117,C_118] : k2_xboole_0(k1_tarski(A_116),k2_tarski(B_117,C_118)) = k1_enumset1(A_116,B_117,C_118) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_407,plain,(
    ! [A_116] : k2_xboole_0(k1_tarski(A_116),k1_tarski('#skF_5')) = k1_enumset1(A_116,'#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_398])).

tff(c_533,plain,(
    ! [A_133] : k1_enumset1(A_133,'#skF_5','#skF_6') = k2_tarski(A_133,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_407])).

tff(c_26,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_553,plain,(
    ! [A_133] : r2_hidden('#skF_6',k2_tarski(A_133,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_26])).

tff(c_54,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_667,plain,(
    ! [E_138,C_139,B_140,A_141] :
      ( E_138 = C_139
      | E_138 = B_140
      | E_138 = A_141
      | ~ r2_hidden(E_138,k1_enumset1(A_141,B_140,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1200,plain,(
    ! [E_2711,B_2712,A_2713] :
      ( E_2711 = B_2712
      | E_2711 = A_2713
      | E_2711 = A_2713
      | ~ r2_hidden(E_2711,k2_tarski(A_2713,B_2712)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_667])).

tff(c_1210,plain,(
    ! [A_133] :
      ( '#skF_5' = '#skF_6'
      | A_133 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_553,c_1200])).

tff(c_1235,plain,(
    ! [A_2714] : A_2714 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1210])).

tff(c_1449,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 3.20/1.52  
% 3.20/1.52  %Foreground sorts:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Background operators:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Foreground operators:
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.20/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.20/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.52  
% 3.37/1.53  tff(f_95, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.37/1.53  tff(f_80, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.37/1.53  tff(f_82, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.37/1.53  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.37/1.53  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.53  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.53  tff(c_48, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(B_30))=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.53  tff(c_309, plain, (![A_108, B_109]: (k2_xboole_0(k1_tarski(A_108), k1_tarski(B_109))=k2_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.53  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.37/1.53  tff(c_315, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_309, c_62])).
% 3.37/1.53  tff(c_398, plain, (![A_116, B_117, C_118]: (k2_xboole_0(k1_tarski(A_116), k2_tarski(B_117, C_118))=k1_enumset1(A_116, B_117, C_118))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.37/1.53  tff(c_407, plain, (![A_116]: (k2_xboole_0(k1_tarski(A_116), k1_tarski('#skF_5'))=k1_enumset1(A_116, '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_315, c_398])).
% 3.37/1.53  tff(c_533, plain, (![A_133]: (k1_enumset1(A_133, '#skF_5', '#skF_6')=k2_tarski(A_133, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_407])).
% 3.37/1.53  tff(c_26, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.37/1.53  tff(c_553, plain, (![A_133]: (r2_hidden('#skF_6', k2_tarski(A_133, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_533, c_26])).
% 3.37/1.53  tff(c_54, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.53  tff(c_667, plain, (![E_138, C_139, B_140, A_141]: (E_138=C_139 | E_138=B_140 | E_138=A_141 | ~r2_hidden(E_138, k1_enumset1(A_141, B_140, C_139)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.37/1.53  tff(c_1200, plain, (![E_2711, B_2712, A_2713]: (E_2711=B_2712 | E_2711=A_2713 | E_2711=A_2713 | ~r2_hidden(E_2711, k2_tarski(A_2713, B_2712)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_667])).
% 3.37/1.53  tff(c_1210, plain, (![A_133]: ('#skF_5'='#skF_6' | A_133='#skF_6')), inference(resolution, [status(thm)], [c_553, c_1200])).
% 3.37/1.53  tff(c_1235, plain, (![A_2714]: (A_2714='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_1210])).
% 3.37/1.53  tff(c_1449, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1235, c_60])).
% 3.37/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.53  
% 3.37/1.53  Inference rules
% 3.37/1.53  ----------------------
% 3.37/1.53  #Ref     : 0
% 3.37/1.53  #Sup     : 422
% 3.37/1.53  #Fact    : 0
% 3.37/1.53  #Define  : 0
% 3.37/1.53  #Split   : 1
% 3.37/1.53  #Chain   : 0
% 3.37/1.53  #Close   : 0
% 3.37/1.53  
% 3.37/1.53  Ordering : KBO
% 3.37/1.53  
% 3.37/1.53  Simplification rules
% 3.37/1.53  ----------------------
% 3.37/1.53  #Subsume      : 52
% 3.37/1.53  #Demod        : 102
% 3.37/1.53  #Tautology    : 116
% 3.37/1.53  #SimpNegUnit  : 15
% 3.37/1.53  #BackRed      : 0
% 3.37/1.53  
% 3.37/1.53  #Partial instantiations: 0
% 3.37/1.53  #Strategies tried      : 1
% 3.37/1.53  
% 3.37/1.53  Timing (in seconds)
% 3.37/1.53  ----------------------
% 3.37/1.54  Preprocessing        : 0.33
% 3.37/1.54  Parsing              : 0.17
% 3.37/1.54  CNF conversion       : 0.03
% 3.37/1.54  Main loop            : 0.44
% 3.37/1.54  Inferencing          : 0.20
% 3.37/1.54  Reduction            : 0.13
% 3.37/1.54  Demodulation         : 0.09
% 3.37/1.54  BG Simplification    : 0.02
% 3.37/1.54  Subsumption          : 0.06
% 3.37/1.54  Abstraction          : 0.02
% 3.37/1.54  MUC search           : 0.00
% 3.37/1.54  Cooper               : 0.00
% 3.37/1.54  Total                : 0.79
% 3.37/1.54  Index Insertion      : 0.00
% 3.37/1.54  Index Deletion       : 0.00
% 3.37/1.54  Index Matching       : 0.00
% 3.37/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
