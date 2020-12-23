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
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   49 (  49 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_148,plain,(
    ! [A_88,B_89] : r1_tarski(A_88,k2_xboole_0(A_88,B_89)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_151,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_148])).

tff(c_275,plain,(
    ! [B_121,A_122] :
      ( B_121 = A_122
      | ~ r1_tarski(B_121,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_277,plain,
    ( k2_tarski('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_151,c_275])).

tff(c_286,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_277])).

tff(c_191,plain,(
    ! [A_107,B_108] : k1_enumset1(A_107,A_107,B_108) = k2_tarski(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_157,plain,(
    ! [E_92,B_93,C_94] : r2_hidden(E_92,k1_enumset1(E_92,B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [E_92,B_93,C_94] : ~ v1_xboole_0(k1_enumset1(E_92,B_93,C_94)) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_202,plain,(
    ! [A_107,B_108] : ~ v1_xboole_0(k2_tarski(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_161])).

tff(c_304,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_202])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.51  
% 2.52/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.51  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 2.52/1.51  
% 2.52/1.51  %Foreground sorts:
% 2.52/1.51  
% 2.52/1.51  
% 2.52/1.51  %Background operators:
% 2.52/1.51  
% 2.52/1.51  
% 2.52/1.51  %Foreground operators:
% 2.52/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.52/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.52/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.52/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.51  
% 2.72/1.52  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.72/1.52  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.52  tff(f_99, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.72/1.52  tff(f_52, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.72/1.52  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.52  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.52  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.72/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.72/1.52  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.52  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.52  tff(c_80, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.52  tff(c_148, plain, (![A_88, B_89]: (r1_tarski(A_88, k2_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.52  tff(c_151, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_148])).
% 2.72/1.52  tff(c_275, plain, (![B_121, A_122]: (B_121=A_122 | ~r1_tarski(B_121, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.72/1.52  tff(c_277, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_151, c_275])).
% 2.72/1.52  tff(c_286, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_277])).
% 2.72/1.52  tff(c_191, plain, (![A_107, B_108]: (k1_enumset1(A_107, A_107, B_108)=k2_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.72/1.52  tff(c_157, plain, (![E_92, B_93, C_94]: (r2_hidden(E_92, k1_enumset1(E_92, B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.72/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.52  tff(c_161, plain, (![E_92, B_93, C_94]: (~v1_xboole_0(k1_enumset1(E_92, B_93, C_94)))), inference(resolution, [status(thm)], [c_157, c_2])).
% 2.72/1.52  tff(c_202, plain, (![A_107, B_108]: (~v1_xboole_0(k2_tarski(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_161])).
% 2.72/1.52  tff(c_304, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_286, c_202])).
% 2.72/1.52  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_304])).
% 2.72/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.52  
% 2.72/1.52  Inference rules
% 2.72/1.52  ----------------------
% 2.72/1.52  #Ref     : 0
% 2.72/1.52  #Sup     : 56
% 2.72/1.52  #Fact    : 0
% 2.72/1.52  #Define  : 0
% 2.72/1.52  #Split   : 0
% 2.72/1.52  #Chain   : 0
% 2.72/1.52  #Close   : 0
% 2.72/1.52  
% 2.72/1.52  Ordering : KBO
% 2.72/1.52  
% 2.72/1.52  Simplification rules
% 2.72/1.52  ----------------------
% 2.72/1.52  #Subsume      : 5
% 2.72/1.52  #Demod        : 12
% 2.72/1.52  #Tautology    : 36
% 2.72/1.52  #SimpNegUnit  : 0
% 2.72/1.52  #BackRed      : 2
% 2.72/1.52  
% 2.72/1.52  #Partial instantiations: 0
% 2.72/1.52  #Strategies tried      : 1
% 2.72/1.52  
% 2.72/1.52  Timing (in seconds)
% 2.72/1.52  ----------------------
% 2.72/1.53  Preprocessing        : 0.46
% 2.72/1.53  Parsing              : 0.24
% 2.72/1.53  CNF conversion       : 0.04
% 2.72/1.53  Main loop            : 0.22
% 2.72/1.53  Inferencing          : 0.07
% 2.72/1.53  Reduction            : 0.08
% 2.72/1.53  Demodulation         : 0.06
% 2.72/1.53  BG Simplification    : 0.03
% 2.72/1.53  Subsumption          : 0.04
% 2.72/1.53  Abstraction          : 0.02
% 2.72/1.53  MUC search           : 0.00
% 2.72/1.53  Cooper               : 0.00
% 2.72/1.53  Total                : 0.72
% 2.72/1.53  Index Insertion      : 0.00
% 2.72/1.53  Index Deletion       : 0.00
% 2.72/1.53  Index Matching       : 0.00
% 2.72/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
