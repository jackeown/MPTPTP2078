%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:29 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 100 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 ( 112 expanded)
%              Number of equality atoms :   17 (  90 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_70,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_23,B_24] :
      ( k1_xboole_0 = A_23
      | k2_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_56,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_24])).

tff(c_85,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_56])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | k2_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_132,plain,(
    ! [A_8] : r1_xboole_0('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_49])).

tff(c_131,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_54])).

tff(c_146,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ r1_xboole_0(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_149,plain,(
    ! [B_31] :
      ( ~ r2_hidden('#skF_1',B_31)
      | ~ r1_xboole_0('#skF_2',B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_146])).

tff(c_151,plain,(
    ! [B_31] : ~ r2_hidden('#skF_1',B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_149])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_300,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | ~ r1_tarski(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_306,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_1',B_47)
      | ~ r1_tarski('#skF_2',B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_300])).

tff(c_309,plain,(
    ! [B_47] : r2_hidden('#skF_1',B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_306])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.17  
% 1.84/1.17  %Foreground sorts:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Background operators:
% 1.84/1.17  
% 1.84/1.17  
% 1.84/1.17  %Foreground operators:
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.17  
% 1.84/1.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.84/1.18  tff(f_58, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.84/1.18  tff(f_35, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.84/1.18  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.84/1.18  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.84/1.18  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.84/1.18  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.84/1.18  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.84/1.18  tff(c_70, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.18  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.18  tff(c_50, plain, (![A_23, B_24]: (k1_xboole_0=A_23 | k2_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.18  tff(c_54, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_50])).
% 1.84/1.18  tff(c_56, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_24])).
% 1.84/1.18  tff(c_85, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_56])).
% 1.84/1.18  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | k2_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.18  tff(c_127, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_85, c_6])).
% 1.84/1.18  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.84/1.18  tff(c_46, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.18  tff(c_49, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 1.84/1.18  tff(c_132, plain, (![A_8]: (r1_xboole_0('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_49])).
% 1.84/1.18  tff(c_131, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_54])).
% 1.84/1.18  tff(c_146, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~r1_xboole_0(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.84/1.18  tff(c_149, plain, (![B_31]: (~r2_hidden('#skF_1', B_31) | ~r1_xboole_0('#skF_2', B_31))), inference(superposition, [status(thm), theory('equality')], [c_131, c_146])).
% 1.84/1.18  tff(c_151, plain, (![B_31]: (~r2_hidden('#skF_1', B_31))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_149])).
% 1.84/1.18  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.18  tff(c_135, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_8])).
% 1.84/1.18  tff(c_300, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | ~r1_tarski(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.18  tff(c_306, plain, (![B_47]: (r2_hidden('#skF_1', B_47) | ~r1_tarski('#skF_2', B_47))), inference(superposition, [status(thm), theory('equality')], [c_131, c_300])).
% 1.84/1.18  tff(c_309, plain, (![B_47]: (r2_hidden('#skF_1', B_47))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_306])).
% 1.84/1.18  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_309])).
% 1.84/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  Inference rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Ref     : 0
% 1.84/1.18  #Sup     : 71
% 1.84/1.18  #Fact    : 0
% 1.84/1.18  #Define  : 0
% 1.84/1.18  #Split   : 0
% 1.84/1.18  #Chain   : 0
% 1.84/1.18  #Close   : 0
% 1.84/1.18  
% 1.84/1.18  Ordering : KBO
% 1.84/1.18  
% 1.84/1.18  Simplification rules
% 1.84/1.18  ----------------------
% 1.84/1.18  #Subsume      : 6
% 1.84/1.18  #Demod        : 38
% 1.84/1.18  #Tautology    : 57
% 1.84/1.18  #SimpNegUnit  : 1
% 1.84/1.18  #BackRed      : 8
% 1.84/1.18  
% 1.84/1.18  #Partial instantiations: 0
% 1.84/1.18  #Strategies tried      : 1
% 1.84/1.18  
% 1.84/1.18  Timing (in seconds)
% 1.84/1.18  ----------------------
% 1.84/1.19  Preprocessing        : 0.28
% 1.84/1.19  Parsing              : 0.15
% 1.84/1.19  CNF conversion       : 0.01
% 1.84/1.19  Main loop            : 0.15
% 1.84/1.19  Inferencing          : 0.06
% 1.84/1.19  Reduction            : 0.05
% 1.84/1.19  Demodulation         : 0.04
% 1.84/1.19  BG Simplification    : 0.01
% 1.84/1.19  Subsumption          : 0.02
% 1.84/1.19  Abstraction          : 0.01
% 1.84/1.19  MUC search           : 0.00
% 1.84/1.19  Cooper               : 0.00
% 1.84/1.19  Total                : 0.45
% 1.84/1.19  Index Insertion      : 0.00
% 1.84/1.19  Index Deletion       : 0.00
% 1.84/1.19  Index Matching       : 0.00
% 1.84/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
