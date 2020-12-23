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
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(k1_tarski(A_16),B_17) = B_17
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,(
    ! [A_20,A_21] :
      ( k2_xboole_0(A_20,k1_tarski(A_21)) = A_20
      | ~ r2_hidden(A_21,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_20,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_19])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:55:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.69/1.10  
% 1.69/1.10  %Foreground sorts:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Background operators:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Foreground operators:
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.10  
% 1.69/1.11  tff(f_50, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.69/1.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.69/1.11  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.69/1.11  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.69/1.11  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.11  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.11  tff(c_64, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), B_17)=B_17 | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.11  tff(c_104, plain, (![A_20, A_21]: (k2_xboole_0(A_20, k1_tarski(A_21))=A_20 | ~r2_hidden(A_21, A_20))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 1.69/1.11  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.11  tff(c_16, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.11  tff(c_19, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.69/1.11  tff(c_20, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_19])).
% 1.69/1.11  tff(c_120, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_104, c_20])).
% 1.69/1.11  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_120])).
% 1.69/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.11  Inference rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Ref     : 0
% 1.69/1.11  #Sup     : 29
% 1.69/1.11  #Fact    : 0
% 1.69/1.11  #Define  : 0
% 1.69/1.11  #Split   : 0
% 1.69/1.11  #Chain   : 0
% 1.69/1.11  #Close   : 0
% 1.69/1.11  
% 1.69/1.11  Ordering : KBO
% 1.69/1.11  
% 1.69/1.11  Simplification rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Subsume      : 2
% 1.69/1.11  #Demod        : 4
% 1.69/1.11  #Tautology    : 15
% 1.69/1.11  #SimpNegUnit  : 0
% 1.69/1.11  #BackRed      : 0
% 1.69/1.11  
% 1.69/1.11  #Partial instantiations: 0
% 1.69/1.11  #Strategies tried      : 1
% 1.69/1.11  
% 1.69/1.11  Timing (in seconds)
% 1.69/1.11  ----------------------
% 1.69/1.11  Preprocessing        : 0.27
% 1.69/1.11  Parsing              : 0.15
% 1.69/1.11  CNF conversion       : 0.01
% 1.69/1.11  Main loop            : 0.10
% 1.69/1.11  Inferencing          : 0.04
% 1.69/1.11  Reduction            : 0.03
% 1.69/1.11  Demodulation         : 0.03
% 1.69/1.11  BG Simplification    : 0.01
% 1.69/1.11  Subsumption          : 0.02
% 1.69/1.11  Abstraction          : 0.01
% 1.69/1.11  MUC search           : 0.00
% 1.69/1.11  Cooper               : 0.00
% 1.69/1.11  Total                : 0.39
% 1.69/1.11  Index Insertion      : 0.00
% 1.69/1.11  Index Deletion       : 0.00
% 1.69/1.11  Index Matching       : 0.00
% 1.69/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
