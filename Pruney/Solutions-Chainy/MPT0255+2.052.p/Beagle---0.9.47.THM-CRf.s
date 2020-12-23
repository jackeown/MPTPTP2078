%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   43 (  43 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_247,plain,(
    ! [A_67,B_68] : k1_enumset1(A_67,A_67,B_68) = k2_tarski(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [E_25,A_19,B_20] : r2_hidden(E_25,k1_enumset1(A_19,B_20,E_25)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_261,plain,(
    ! [B_68,A_67] : r2_hidden(B_68,k2_tarski(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_22])).

tff(c_16,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_188,plain,(
    ! [A_63,B_64] : k3_xboole_0(A_63,k2_xboole_0(A_63,B_64)) = A_63 ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_206,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_188])).

tff(c_293,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_296,plain,(
    ! [C_79] :
      ( ~ r1_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0)
      | ~ r2_hidden(C_79,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_293])).

tff(c_424,plain,(
    ! [C_88] : ~ r2_hidden(C_88,k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_296])).

tff(c_436,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_261,c_424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.08/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.33  
% 2.40/1.34  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.40/1.34  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.40/1.34  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.40/1.34  tff(f_90, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.40/1.34  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.40/1.34  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.40/1.34  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.40/1.34  tff(c_247, plain, (![A_67, B_68]: (k1_enumset1(A_67, A_67, B_68)=k2_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.34  tff(c_22, plain, (![E_25, A_19, B_20]: (r2_hidden(E_25, k1_enumset1(A_19, B_20, E_25)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.40/1.34  tff(c_261, plain, (![B_68, A_67]: (r2_hidden(B_68, k2_tarski(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_22])).
% 2.40/1.34  tff(c_16, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.34  tff(c_52, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.40/1.34  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.40/1.34  tff(c_153, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.34  tff(c_188, plain, (![A_63, B_64]: (k3_xboole_0(A_63, k2_xboole_0(A_63, B_64))=A_63)), inference(resolution, [status(thm)], [c_18, c_153])).
% 2.40/1.34  tff(c_206, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_52, c_188])).
% 2.40/1.34  tff(c_293, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.34  tff(c_296, plain, (![C_79]: (~r1_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0) | ~r2_hidden(C_79, k2_tarski('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_206, c_293])).
% 2.40/1.34  tff(c_424, plain, (![C_88]: (~r2_hidden(C_88, k2_tarski('#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_296])).
% 2.40/1.34  tff(c_436, plain, $false, inference(resolution, [status(thm)], [c_261, c_424])).
% 2.40/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  Inference rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Ref     : 0
% 2.40/1.34  #Sup     : 96
% 2.40/1.34  #Fact    : 0
% 2.40/1.34  #Define  : 0
% 2.40/1.34  #Split   : 0
% 2.40/1.34  #Chain   : 0
% 2.40/1.34  #Close   : 0
% 2.40/1.34  
% 2.40/1.34  Ordering : KBO
% 2.40/1.34  
% 2.40/1.34  Simplification rules
% 2.40/1.34  ----------------------
% 2.40/1.34  #Subsume      : 5
% 2.40/1.34  #Demod        : 31
% 2.40/1.34  #Tautology    : 56
% 2.40/1.34  #SimpNegUnit  : 1
% 2.40/1.34  #BackRed      : 9
% 2.40/1.34  
% 2.40/1.34  #Partial instantiations: 0
% 2.40/1.34  #Strategies tried      : 1
% 2.40/1.34  
% 2.40/1.34  Timing (in seconds)
% 2.40/1.34  ----------------------
% 2.40/1.34  Preprocessing        : 0.32
% 2.40/1.34  Parsing              : 0.17
% 2.40/1.34  CNF conversion       : 0.03
% 2.40/1.34  Main loop            : 0.21
% 2.40/1.34  Inferencing          : 0.07
% 2.40/1.34  Reduction            : 0.08
% 2.40/1.34  Demodulation         : 0.06
% 2.40/1.34  BG Simplification    : 0.01
% 2.40/1.34  Subsumption          : 0.03
% 2.40/1.34  Abstraction          : 0.01
% 2.40/1.34  MUC search           : 0.00
% 2.40/1.34  Cooper               : 0.00
% 2.40/1.34  Total                : 0.56
% 2.40/1.34  Index Insertion      : 0.00
% 2.40/1.34  Index Deletion       : 0.00
% 2.40/1.34  Index Matching       : 0.00
% 2.40/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
