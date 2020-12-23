%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  30 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_74,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),B_23)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_20])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(k1_tarski(A_31),B_32) = k1_tarski(A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(B_33,k1_tarski(A_34)) = k1_tarski(A_34)
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2])).

tff(c_18,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_21,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_131,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_21])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.16  
% 1.72/1.17  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.72/1.17  tff(f_51, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.72/1.17  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.72/1.17  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.72/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.72/1.17  tff(c_74, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), B_23) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.17  tff(c_20, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.17  tff(c_78, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_20])).
% 1.72/1.17  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.17  tff(c_84, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.17  tff(c_98, plain, (![A_31, B_32]: (k3_xboole_0(k1_tarski(A_31), B_32)=k1_tarski(A_31) | ~r2_hidden(A_31, B_32))), inference(resolution, [status(thm)], [c_14, c_84])).
% 1.72/1.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.17  tff(c_121, plain, (![B_33, A_34]: (k3_xboole_0(B_33, k1_tarski(A_34))=k1_tarski(A_34) | ~r2_hidden(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2])).
% 1.72/1.17  tff(c_18, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.17  tff(c_21, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 1.72/1.17  tff(c_131, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_21])).
% 1.72/1.17  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_131])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 32
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 0
% 1.72/1.17  #Demod        : 2
% 1.72/1.17  #Tautology    : 18
% 1.72/1.17  #SimpNegUnit  : 0
% 1.72/1.17  #BackRed      : 0
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.72/1.17  Preprocessing        : 0.30
% 1.72/1.17  Parsing              : 0.16
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.13
% 1.72/1.17  Inferencing          : 0.06
% 1.72/1.17  Reduction            : 0.04
% 1.72/1.17  Demodulation         : 0.03
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.02
% 1.72/1.17  Abstraction          : 0.01
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.45
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
