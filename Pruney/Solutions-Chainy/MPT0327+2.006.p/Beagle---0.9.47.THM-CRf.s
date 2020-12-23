%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:31 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  48 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_tarski(A_24),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(k1_tarski(A_41),B_42) = B_42
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [B_33,A_34] : k3_tarski(k2_tarski(B_33,A_34)) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_20,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_241,plain,(
    ! [B_43,A_44] :
      ( k2_xboole_0(B_43,k1_tarski(A_44)) = B_43
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_128])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_22])).

tff(c_240,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_6,c_148])).

tff(c_247,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_240])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_52, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.93/1.21  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.93/1.21  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.93/1.21  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.93/1.21  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.93/1.21  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.21  tff(c_68, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.21  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.21  tff(c_201, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)=B_42 | ~r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_68, c_4])).
% 1.93/1.21  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.21  tff(c_87, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.21  tff(c_122, plain, (![B_33, A_34]: (k3_tarski(k2_tarski(B_33, A_34))=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 1.93/1.21  tff(c_20, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.21  tff(c_128, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 1.93/1.21  tff(c_241, plain, (![B_43, A_44]: (k2_xboole_0(B_43, k1_tarski(A_44))=B_43 | ~r2_hidden(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_201, c_128])).
% 1.93/1.21  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_22, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.21  tff(c_148, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_22])).
% 1.93/1.21  tff(c_240, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_6, c_148])).
% 1.93/1.21  tff(c_247, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_241, c_240])).
% 1.93/1.21  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_247])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 0
% 1.93/1.21  #Sup     : 63
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 2
% 1.93/1.21  #Demod        : 7
% 1.93/1.21  #Tautology    : 39
% 1.93/1.21  #SimpNegUnit  : 0
% 1.93/1.21  #BackRed      : 1
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.28
% 1.93/1.21  Parsing              : 0.15
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.15
% 1.93/1.21  Inferencing          : 0.06
% 1.93/1.21  Reduction            : 0.05
% 1.93/1.21  Demodulation         : 0.04
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.46
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
