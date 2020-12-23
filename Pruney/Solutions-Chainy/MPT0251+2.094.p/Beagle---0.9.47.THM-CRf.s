%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:59 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(k2_tarski(A_37,B_38),C_39)
      | ~ r2_hidden(B_38,C_39)
      | ~ r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_40,C_41] :
      ( r1_tarski(k1_tarski(A_40),C_41)
      | ~ r2_hidden(A_40,C_41)
      | ~ r2_hidden(A_40,C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [A_45,C_46] :
      ( k2_xboole_0(k1_tarski(A_45),C_46) = C_46
      | ~ r2_hidden(A_45,C_46) ) ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [C_47,A_48] :
      ( k2_xboole_0(C_47,k1_tarski(A_48)) = C_47
      | ~ r2_hidden(A_48,C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2])).

tff(c_20,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_235,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_23])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.25  
% 1.89/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.25  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.89/1.25  
% 1.89/1.25  %Foreground sorts:
% 1.89/1.25  
% 1.89/1.25  
% 1.89/1.25  %Background operators:
% 1.89/1.25  
% 1.89/1.25  
% 1.89/1.25  %Foreground operators:
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.25  
% 1.89/1.26  tff(f_50, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.89/1.26  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.26  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.26  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.89/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.89/1.26  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.26  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.26  tff(c_121, plain, (![A_37, B_38, C_39]: (r1_tarski(k2_tarski(A_37, B_38), C_39) | ~r2_hidden(B_38, C_39) | ~r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.26  tff(c_137, plain, (![A_40, C_41]: (r1_tarski(k1_tarski(A_40), C_41) | ~r2_hidden(A_40, C_41) | ~r2_hidden(A_40, C_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 1.89/1.26  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.26  tff(c_180, plain, (![A_45, C_46]: (k2_xboole_0(k1_tarski(A_45), C_46)=C_46 | ~r2_hidden(A_45, C_46))), inference(resolution, [status(thm)], [c_137, c_4])).
% 1.89/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.26  tff(c_211, plain, (![C_47, A_48]: (k2_xboole_0(C_47, k1_tarski(A_48))=C_47 | ~r2_hidden(A_48, C_47))), inference(superposition, [status(thm), theory('equality')], [c_180, c_2])).
% 1.89/1.26  tff(c_20, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.26  tff(c_23, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.89/1.26  tff(c_235, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_211, c_23])).
% 1.89/1.26  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_235])).
% 1.89/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.26  
% 1.89/1.26  Inference rules
% 1.89/1.26  ----------------------
% 1.89/1.26  #Ref     : 0
% 1.89/1.26  #Sup     : 59
% 1.89/1.26  #Fact    : 0
% 1.89/1.26  #Define  : 0
% 1.89/1.26  #Split   : 0
% 1.89/1.26  #Chain   : 0
% 1.89/1.26  #Close   : 0
% 1.89/1.26  
% 1.89/1.26  Ordering : KBO
% 1.89/1.26  
% 1.89/1.26  Simplification rules
% 1.89/1.26  ----------------------
% 1.89/1.26  #Subsume      : 5
% 1.89/1.26  #Demod        : 2
% 1.89/1.26  #Tautology    : 26
% 1.89/1.26  #SimpNegUnit  : 0
% 1.89/1.26  #BackRed      : 0
% 1.89/1.26  
% 1.89/1.26  #Partial instantiations: 0
% 1.89/1.26  #Strategies tried      : 1
% 1.89/1.26  
% 1.89/1.26  Timing (in seconds)
% 1.89/1.26  ----------------------
% 1.89/1.26  Preprocessing        : 0.30
% 1.89/1.26  Parsing              : 0.16
% 1.89/1.26  CNF conversion       : 0.02
% 1.89/1.26  Main loop            : 0.15
% 1.89/1.26  Inferencing          : 0.07
% 1.89/1.26  Reduction            : 0.05
% 1.89/1.26  Demodulation         : 0.04
% 1.89/1.26  BG Simplification    : 0.01
% 1.89/1.26  Subsumption          : 0.02
% 1.89/1.26  Abstraction          : 0.01
% 1.89/1.26  MUC search           : 0.00
% 1.89/1.26  Cooper               : 0.00
% 1.89/1.26  Total                : 0.47
% 1.89/1.26  Index Insertion      : 0.00
% 1.89/1.26  Index Deletion       : 0.00
% 1.89/1.26  Index Matching       : 0.00
% 1.89/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
