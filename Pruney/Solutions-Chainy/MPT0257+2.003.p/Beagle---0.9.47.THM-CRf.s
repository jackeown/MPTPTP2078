%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:05 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(k1_tarski(A_32),B_33) = k1_tarski(A_32)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_296,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(k1_tarski(A_56),B_57) = k1_tarski(A_56)
      | r2_hidden(A_56,k4_xboole_0(k1_tarski(A_56),B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_327,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden(A_58,B_59)
      | k3_xboole_0(k1_tarski(A_58),B_59) = k1_tarski(A_58) ) ),
    inference(resolution,[status(thm)],[c_296,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_362,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(B_60,k1_tarski(A_61)) = k1_tarski(A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_2])).

tff(c_32,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_390,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_32])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.25  
% 2.16/1.26  tff(f_53, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 2.16/1.26  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.16/1.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.26  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.16/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.16/1.26  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.26  tff(c_116, plain, (![A_32, B_33]: (k4_xboole_0(k1_tarski(A_32), B_33)=k1_tarski(A_32) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.26  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.26  tff(c_296, plain, (![A_56, B_57]: (k3_xboole_0(k1_tarski(A_56), B_57)=k1_tarski(A_56) | r2_hidden(A_56, k4_xboole_0(k1_tarski(A_56), B_57)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_22])).
% 2.16/1.26  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.26  tff(c_327, plain, (![A_58, B_59]: (~r2_hidden(A_58, B_59) | k3_xboole_0(k1_tarski(A_58), B_59)=k1_tarski(A_58))), inference(resolution, [status(thm)], [c_296, c_6])).
% 2.16/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.26  tff(c_362, plain, (![B_60, A_61]: (k3_xboole_0(B_60, k1_tarski(A_61))=k1_tarski(A_61) | ~r2_hidden(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_327, c_2])).
% 2.16/1.26  tff(c_32, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.26  tff(c_390, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_362, c_32])).
% 2.16/1.26  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_390])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 98
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 0
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 8
% 2.16/1.26  #Demod        : 5
% 2.16/1.26  #Tautology    : 36
% 2.16/1.26  #SimpNegUnit  : 0
% 2.16/1.26  #BackRed      : 0
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.30
% 2.16/1.26  Parsing              : 0.15
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.21
% 2.16/1.26  Inferencing          : 0.08
% 2.16/1.26  Reduction            : 0.07
% 2.16/1.26  Demodulation         : 0.05
% 2.16/1.26  BG Simplification    : 0.02
% 2.16/1.26  Subsumption          : 0.04
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.53
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
