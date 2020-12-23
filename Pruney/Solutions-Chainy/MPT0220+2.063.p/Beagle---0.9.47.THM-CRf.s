%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_enumset1(A_6,A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k2_tarski(A_11,B_12),k2_tarski(C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_5,C_13,D_14] : k2_xboole_0(k1_tarski(A_5),k2_tarski(C_13,D_14)) = k2_enumset1(A_5,A_5,C_13,D_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_8,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:53:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.06  
% 1.54/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.06  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.54/1.06  
% 1.54/1.06  %Foreground sorts:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Background operators:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Foreground operators:
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.54/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.54/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.06  
% 1.54/1.07  tff(f_31, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 1.54/1.07  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.54/1.07  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 1.54/1.07  tff(f_34, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.54/1.07  tff(c_6, plain, (![A_6, B_7]: (k2_enumset1(A_6, A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.07  tff(c_4, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.07  tff(c_27, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k2_tarski(A_11, B_12), k2_tarski(C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.07  tff(c_36, plain, (![A_5, C_13, D_14]: (k2_xboole_0(k1_tarski(A_5), k2_tarski(C_13, D_14))=k2_enumset1(A_5, A_5, C_13, D_14))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27])).
% 1.54/1.07  tff(c_8, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.54/1.07  tff(c_42, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 1.54/1.07  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_42])).
% 1.54/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.07  
% 1.54/1.07  Inference rules
% 1.54/1.07  ----------------------
% 1.54/1.07  #Ref     : 0
% 1.54/1.07  #Sup     : 8
% 1.54/1.07  #Fact    : 0
% 1.54/1.07  #Define  : 0
% 1.54/1.07  #Split   : 0
% 1.54/1.07  #Chain   : 0
% 1.54/1.07  #Close   : 0
% 1.54/1.07  
% 1.54/1.07  Ordering : KBO
% 1.54/1.07  
% 1.54/1.07  Simplification rules
% 1.54/1.07  ----------------------
% 1.54/1.07  #Subsume      : 0
% 1.54/1.07  #Demod        : 2
% 1.54/1.07  #Tautology    : 6
% 1.54/1.07  #SimpNegUnit  : 0
% 1.54/1.07  #BackRed      : 1
% 1.54/1.07  
% 1.54/1.07  #Partial instantiations: 0
% 1.54/1.07  #Strategies tried      : 1
% 1.54/1.07  
% 1.54/1.07  Timing (in seconds)
% 1.54/1.07  ----------------------
% 1.54/1.07  Preprocessing        : 0.26
% 1.54/1.07  Parsing              : 0.14
% 1.54/1.07  CNF conversion       : 0.01
% 1.54/1.07  Main loop            : 0.06
% 1.54/1.07  Inferencing          : 0.03
% 1.54/1.07  Reduction            : 0.02
% 1.54/1.07  Demodulation         : 0.02
% 1.54/1.07  BG Simplification    : 0.01
% 1.54/1.07  Subsumption          : 0.01
% 1.54/1.07  Abstraction          : 0.01
% 1.54/1.07  MUC search           : 0.00
% 1.54/1.07  Cooper               : 0.00
% 1.54/1.07  Total                : 0.35
% 1.54/1.07  Index Insertion      : 0.00
% 1.54/1.07  Index Deletion       : 0.00
% 1.54/1.07  Index Matching       : 0.00
% 1.54/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
