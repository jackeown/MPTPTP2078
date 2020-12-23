%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:23 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   31 (  95 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 ( 136 expanded)
%              Number of equality atoms :   18 (  78 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(k1_xboole_0,k1_tarski(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    ! [C_17,A_18,B_19] :
      ( C_17 = A_18
      | ~ r1_tarski(k2_tarski(A_18,B_19),k1_tarski(C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_16,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_47,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_73,plain,(
    ! [B_25,A_26] :
      ( k1_tarski(B_25) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_73])).

tff(c_85,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_76])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( C_11 = A_9
      | ~ r1_tarski(k2_tarski(A_9,B_10),k1_tarski(C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [C_11] :
      ( C_11 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_100,plain,(
    ! [C_11] : C_11 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_91,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_48])).

tff(c_133,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_91])).

tff(c_137,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.23  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.23  
% 1.84/1.23  %Foreground sorts:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Background operators:
% 1.84/1.23  
% 1.84/1.23  
% 1.84/1.23  %Foreground operators:
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.84/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.23  
% 1.84/1.24  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.84/1.24  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 1.84/1.24  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.84/1.24  tff(c_12, plain, (![B_8]: (r1_tarski(k1_xboole_0, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.24  tff(c_18, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.24  tff(c_39, plain, (![C_17, A_18, B_19]: (C_17=A_18 | ~r1_tarski(k2_tarski(A_18, B_19), k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.24  tff(c_46, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_18, c_39])).
% 1.84/1.24  tff(c_16, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.24  tff(c_48, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 1.84/1.24  tff(c_47, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_18])).
% 1.84/1.24  tff(c_73, plain, (![B_25, A_26]: (k1_tarski(B_25)=A_26 | k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.24  tff(c_76, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_73])).
% 1.84/1.24  tff(c_85, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_76])).
% 1.84/1.24  tff(c_14, plain, (![C_11, A_9, B_10]: (C_11=A_9 | ~r1_tarski(k2_tarski(A_9, B_10), k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.24  tff(c_96, plain, (![C_11]: (C_11='#skF_1' | ~r1_tarski(k1_xboole_0, k1_tarski(C_11)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 1.84/1.24  tff(c_100, plain, (![C_11]: (C_11='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_96])).
% 1.84/1.24  tff(c_91, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_48])).
% 1.84/1.24  tff(c_133, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_100, c_91])).
% 1.84/1.24  tff(c_137, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_100, c_133])).
% 1.84/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.24  
% 1.84/1.24  Inference rules
% 1.84/1.24  ----------------------
% 1.84/1.24  #Ref     : 0
% 1.84/1.24  #Sup     : 35
% 1.84/1.24  #Fact    : 0
% 1.84/1.24  #Define  : 0
% 1.84/1.24  #Split   : 0
% 1.84/1.24  #Chain   : 0
% 1.84/1.24  #Close   : 0
% 1.84/1.24  
% 1.84/1.24  Ordering : KBO
% 1.84/1.24  
% 1.84/1.24  Simplification rules
% 1.84/1.24  ----------------------
% 1.84/1.24  #Subsume      : 5
% 1.84/1.24  #Demod        : 6
% 1.84/1.24  #Tautology    : 15
% 1.84/1.24  #SimpNegUnit  : 1
% 1.84/1.24  #BackRed      : 4
% 1.84/1.24  
% 1.84/1.24  #Partial instantiations: 0
% 1.84/1.24  #Strategies tried      : 1
% 1.84/1.24  
% 1.84/1.24  Timing (in seconds)
% 1.84/1.24  ----------------------
% 1.84/1.24  Preprocessing        : 0.29
% 1.84/1.24  Parsing              : 0.15
% 1.84/1.24  CNF conversion       : 0.02
% 1.84/1.24  Main loop            : 0.12
% 1.84/1.24  Inferencing          : 0.05
% 1.84/1.24  Reduction            : 0.03
% 1.84/1.24  Demodulation         : 0.03
% 1.84/1.24  BG Simplification    : 0.01
% 1.84/1.24  Subsumption          : 0.02
% 1.84/1.24  Abstraction          : 0.01
% 1.84/1.24  MUC search           : 0.00
% 1.84/1.24  Cooper               : 0.00
% 1.84/1.24  Total                : 0.43
% 1.84/1.24  Index Insertion      : 0.00
% 1.84/1.24  Index Deletion       : 0.00
% 1.84/1.24  Index Matching       : 0.00
% 1.84/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
