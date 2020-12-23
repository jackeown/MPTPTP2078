%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(k1_tarski(A_30),B_31) = B_31
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [B_32,A_33] :
      ( k2_xboole_0(B_32,k1_tarski(A_33)) = B_32
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_26,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_25])).

tff(c_154,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_26])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.24  
% 1.93/1.25  tff(f_59, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.93/1.25  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.93/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.93/1.25  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.93/1.25  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.25  tff(c_107, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)=B_31 | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.25  tff(c_138, plain, (![B_32, A_33]: (k2_xboole_0(B_32, k1_tarski(A_33))=B_32 | ~r2_hidden(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_107, c_2])).
% 1.93/1.25  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.25  tff(c_22, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.25  tff(c_25, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.93/1.25  tff(c_26, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_25])).
% 1.93/1.25  tff(c_154, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_138, c_26])).
% 1.93/1.25  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 35
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 0
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 2
% 1.93/1.25  #Demod        : 9
% 1.93/1.25  #Tautology    : 19
% 1.93/1.25  #SimpNegUnit  : 0
% 1.93/1.25  #BackRed      : 0
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.26  Preprocessing        : 0.26
% 1.93/1.26  Parsing              : 0.13
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.16
% 1.93/1.26  Inferencing          : 0.06
% 1.93/1.26  Reduction            : 0.05
% 1.93/1.26  Demodulation         : 0.04
% 1.93/1.26  BG Simplification    : 0.01
% 1.93/1.26  Subsumption          : 0.03
% 1.93/1.26  Abstraction          : 0.01
% 1.93/1.26  MUC search           : 0.00
% 1.93/1.26  Cooper               : 0.00
% 1.93/1.26  Total                : 0.46
% 1.93/1.26  Index Insertion      : 0.00
% 1.93/1.26  Index Deletion       : 0.00
% 1.93/1.26  Index Matching       : 0.00
% 1.93/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
