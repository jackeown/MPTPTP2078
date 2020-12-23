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
% DateTime   : Thu Dec  3 09:43:10 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  70 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_31,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_31])).

tff(c_48,plain,(
    ! [A_19,C_20,B_21] :
      ( r1_tarski(A_19,C_20)
      | ~ r1_tarski(k2_xboole_0(A_19,B_21),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [C_23] :
      ( r1_tarski('#skF_1',C_23)
      | ~ r1_tarski('#skF_2',C_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_68,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_73,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_16])).

tff(c_96,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_88])).

tff(c_101,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_18])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( ~ r2_xboole_0(B_13,A_14)
      | ~ r2_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_25,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_89,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_73,c_25])).

tff(c_137,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_89])).

tff(c_144,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_20])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:10:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.13  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.81/1.13  
% 1.81/1.13  %Foreground sorts:
% 1.81/1.13  
% 1.81/1.13  
% 1.81/1.13  %Background operators:
% 1.81/1.13  
% 1.81/1.13  
% 1.81/1.13  %Foreground operators:
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.13  
% 1.81/1.14  tff(f_40, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.81/1.14  tff(f_55, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.81/1.14  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.81/1.14  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.81/1.14  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.81/1.14  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.81/1.14  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.14  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.14  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.14  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.14  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_26])).
% 1.81/1.14  tff(c_31, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.14  tff(c_38, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_31])).
% 1.81/1.14  tff(c_48, plain, (![A_19, C_20, B_21]: (r1_tarski(A_19, C_20) | ~r1_tarski(k2_xboole_0(A_19, B_21), C_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.14  tff(c_60, plain, (![C_23]: (r1_tarski('#skF_1', C_23) | ~r1_tarski('#skF_2', C_23))), inference(superposition, [status(thm), theory('equality')], [c_38, c_48])).
% 1.81/1.14  tff(c_68, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_60])).
% 1.81/1.14  tff(c_73, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.14  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.81/1.14  tff(c_88, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_73, c_16])).
% 1.81/1.14  tff(c_96, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_88])).
% 1.81/1.14  tff(c_101, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_18])).
% 1.81/1.14  tff(c_22, plain, (![B_13, A_14]: (~r2_xboole_0(B_13, A_14) | ~r2_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.81/1.14  tff(c_25, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_22])).
% 1.81/1.14  tff(c_89, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_73, c_25])).
% 1.81/1.14  tff(c_137, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_89])).
% 1.81/1.14  tff(c_144, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_20])).
% 1.81/1.14  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_144])).
% 1.81/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.14  
% 1.81/1.14  Inference rules
% 1.81/1.14  ----------------------
% 1.81/1.14  #Ref     : 0
% 1.81/1.14  #Sup     : 30
% 1.81/1.14  #Fact    : 0
% 1.81/1.14  #Define  : 0
% 1.81/1.14  #Split   : 0
% 1.81/1.14  #Chain   : 0
% 1.81/1.14  #Close   : 0
% 1.81/1.14  
% 1.81/1.14  Ordering : KBO
% 1.81/1.14  
% 1.81/1.14  Simplification rules
% 1.81/1.14  ----------------------
% 1.81/1.14  #Subsume      : 3
% 1.81/1.14  #Demod        : 25
% 1.81/1.14  #Tautology    : 21
% 1.81/1.14  #SimpNegUnit  : 1
% 1.81/1.14  #BackRed      : 11
% 1.81/1.14  
% 1.81/1.14  #Partial instantiations: 0
% 1.81/1.14  #Strategies tried      : 1
% 1.81/1.14  
% 1.81/1.14  Timing (in seconds)
% 1.81/1.14  ----------------------
% 1.81/1.14  Preprocessing        : 0.26
% 1.81/1.14  Parsing              : 0.14
% 1.81/1.14  CNF conversion       : 0.02
% 1.81/1.14  Main loop            : 0.14
% 1.81/1.14  Inferencing          : 0.05
% 1.81/1.14  Reduction            : 0.04
% 1.81/1.14  Demodulation         : 0.03
% 1.81/1.14  BG Simplification    : 0.01
% 1.81/1.14  Subsumption          : 0.02
% 1.81/1.14  Abstraction          : 0.01
% 1.81/1.14  MUC search           : 0.00
% 1.81/1.14  Cooper               : 0.00
% 1.81/1.14  Total                : 0.42
% 1.81/1.14  Index Insertion      : 0.00
% 1.81/1.14  Index Deletion       : 0.00
% 1.81/1.14  Index Matching       : 0.00
% 1.81/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
