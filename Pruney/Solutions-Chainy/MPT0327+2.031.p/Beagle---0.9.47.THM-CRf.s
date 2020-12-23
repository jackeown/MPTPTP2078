%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_12,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(k1_tarski(A_15),B_16) = B_16
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_6])).

tff(c_139,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_164,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_13])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_164])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.92/1.25  
% 1.92/1.25  %Foreground sorts:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Background operators:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Foreground operators:
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.25  
% 1.92/1.26  tff(f_42, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.92/1.26  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.92/1.26  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.26  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.92/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.26  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.26  tff(c_64, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), B_16)=B_16 | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.26  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.26  tff(c_82, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(superposition, [status(thm), theory('equality')], [c_64, c_6])).
% 1.92/1.26  tff(c_139, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k4_xboole_0(B_24, A_23))=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.26  tff(c_10, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.26  tff(c_13, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.92/1.26  tff(c_164, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_13])).
% 1.92/1.26  tff(c_168, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_164])).
% 1.92/1.26  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_168])).
% 1.92/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  Inference rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Ref     : 0
% 1.92/1.26  #Sup     : 40
% 1.92/1.26  #Fact    : 0
% 1.92/1.26  #Define  : 0
% 1.92/1.26  #Split   : 1
% 1.92/1.26  #Chain   : 0
% 1.92/1.26  #Close   : 0
% 1.92/1.26  
% 1.92/1.26  Ordering : KBO
% 1.92/1.26  
% 1.92/1.26  Simplification rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Subsume      : 8
% 1.92/1.26  #Demod        : 5
% 1.92/1.26  #Tautology    : 18
% 1.92/1.26  #SimpNegUnit  : 0
% 1.92/1.26  #BackRed      : 0
% 1.92/1.26  
% 1.92/1.26  #Partial instantiations: 0
% 1.92/1.26  #Strategies tried      : 1
% 1.92/1.26  
% 1.92/1.26  Timing (in seconds)
% 1.92/1.26  ----------------------
% 1.92/1.26  Preprocessing        : 0.29
% 1.92/1.26  Parsing              : 0.16
% 1.92/1.26  CNF conversion       : 0.02
% 1.92/1.27  Main loop            : 0.14
% 1.92/1.27  Inferencing          : 0.05
% 1.92/1.27  Reduction            : 0.05
% 1.92/1.27  Demodulation         : 0.04
% 1.92/1.27  BG Simplification    : 0.01
% 1.92/1.27  Subsumption          : 0.02
% 1.92/1.27  Abstraction          : 0.01
% 1.92/1.27  MUC search           : 0.00
% 1.92/1.27  Cooper               : 0.00
% 1.92/1.27  Total                : 0.46
% 1.92/1.27  Index Insertion      : 0.00
% 1.92/1.27  Index Deletion       : 0.00
% 1.92/1.27  Index Matching       : 0.00
% 1.92/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
