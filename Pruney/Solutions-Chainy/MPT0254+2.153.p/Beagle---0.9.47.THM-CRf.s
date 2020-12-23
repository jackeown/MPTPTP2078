%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:38 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | k2_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_31,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_1',B_14)
      | ~ r1_tarski(k1_xboole_0,B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_31])).

tff(c_36,plain,(
    ! [B_14] : r2_hidden('#skF_1',B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_34])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | ~ r1_xboole_0(k1_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_73,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.18  
% 1.67/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.19  
% 1.67/1.19  %Foreground sorts:
% 1.67/1.19  
% 1.67/1.19  
% 1.67/1.19  %Background operators:
% 1.67/1.19  
% 1.67/1.19  
% 1.67/1.19  %Foreground operators:
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.19  
% 1.67/1.20  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.67/1.20  tff(f_46, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.67/1.20  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.67/1.20  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.67/1.20  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.67/1.20  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.67/1.20  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.20  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.20  tff(c_21, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | k2_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.20  tff(c_25, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_21])).
% 1.67/1.20  tff(c_31, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.20  tff(c_34, plain, (![B_14]: (r2_hidden('#skF_1', B_14) | ~r1_tarski(k1_xboole_0, B_14))), inference(superposition, [status(thm), theory('equality')], [c_25, c_31])).
% 1.67/1.20  tff(c_36, plain, (![B_14]: (r2_hidden('#skF_1', B_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_34])).
% 1.67/1.20  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.20  tff(c_57, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | ~r1_xboole_0(k1_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.67/1.20  tff(c_68, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_57])).
% 1.67/1.20  tff(c_73, plain, $false, inference(resolution, [status(thm)], [c_36, c_68])).
% 1.67/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.20  
% 1.67/1.20  Inference rules
% 1.67/1.20  ----------------------
% 1.67/1.20  #Ref     : 0
% 1.67/1.20  #Sup     : 14
% 1.67/1.20  #Fact    : 0
% 1.67/1.20  #Define  : 0
% 1.67/1.20  #Split   : 0
% 1.67/1.20  #Chain   : 0
% 1.67/1.20  #Close   : 0
% 1.67/1.20  
% 1.67/1.20  Ordering : KBO
% 1.67/1.20  
% 1.67/1.20  Simplification rules
% 1.67/1.20  ----------------------
% 1.67/1.20  #Subsume      : 0
% 1.67/1.20  #Demod        : 5
% 1.67/1.20  #Tautology    : 9
% 1.67/1.20  #SimpNegUnit  : 0
% 1.67/1.20  #BackRed      : 1
% 1.67/1.20  
% 1.67/1.20  #Partial instantiations: 0
% 1.67/1.20  #Strategies tried      : 1
% 1.67/1.20  
% 1.67/1.20  Timing (in seconds)
% 1.67/1.20  ----------------------
% 1.67/1.21  Preprocessing        : 0.32
% 1.67/1.21  Parsing              : 0.15
% 1.67/1.21  CNF conversion       : 0.03
% 1.67/1.21  Main loop            : 0.11
% 1.67/1.21  Inferencing          : 0.04
% 1.67/1.21  Reduction            : 0.03
% 1.67/1.21  Demodulation         : 0.02
% 1.67/1.21  BG Simplification    : 0.01
% 1.67/1.21  Subsumption          : 0.02
% 1.67/1.21  Abstraction          : 0.01
% 1.67/1.21  MUC search           : 0.00
% 1.67/1.21  Cooper               : 0.00
% 1.67/1.21  Total                : 0.46
% 1.67/1.21  Index Insertion      : 0.00
% 1.67/1.21  Index Deletion       : 0.00
% 1.67/1.21  Index Matching       : 0.00
% 1.67/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
