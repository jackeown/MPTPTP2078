%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:29 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 113 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 ( 130 expanded)
%              Number of equality atoms :   24 ( 123 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_22,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_37,plain,(
    ! [A_17,B_18] :
      ( k1_xboole_0 = A_17
      | k2_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_37])).

tff(c_42,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | k2_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_8])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = '#skF_2'
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_6])).

tff(c_247,plain,(
    ! [A_7] : k4_xboole_0('#skF_2',A_7) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_119,c_239])).

tff(c_117,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_41])).

tff(c_154,plain,(
    ! [B_26] : k4_xboole_0(k1_tarski(B_26),k1_tarski(B_26)) != k1_tarski(B_26) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_157,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_154])).

tff(c_161,plain,(
    k4_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_157])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.26  
% 1.96/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.26  %$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.96/1.26  
% 1.96/1.26  %Foreground sorts:
% 1.96/1.26  
% 1.96/1.26  
% 1.96/1.26  %Background operators:
% 1.96/1.26  
% 1.96/1.26  
% 1.96/1.26  %Foreground operators:
% 1.96/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.26  
% 1.96/1.27  tff(f_52, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.96/1.27  tff(f_35, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.96/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.96/1.27  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.96/1.27  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.96/1.27  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.96/1.27  tff(c_22, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.27  tff(c_37, plain, (![A_17, B_18]: (k1_xboole_0=A_17 | k2_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.27  tff(c_41, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_37])).
% 1.96/1.27  tff(c_42, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_41, c_22])).
% 1.96/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.27  tff(c_89, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.96/1.27  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | k2_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.27  tff(c_113, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_89, c_8])).
% 1.96/1.27  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.27  tff(c_119, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_10])).
% 1.96/1.27  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.27  tff(c_239, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)='#skF_2' | ~r1_tarski(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_6])).
% 1.96/1.27  tff(c_247, plain, (![A_7]: (k4_xboole_0('#skF_2', A_7)='#skF_2')), inference(resolution, [status(thm)], [c_119, c_239])).
% 1.96/1.27  tff(c_117, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_41])).
% 1.96/1.27  tff(c_154, plain, (![B_26]: (k4_xboole_0(k1_tarski(B_26), k1_tarski(B_26))!=k1_tarski(B_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.27  tff(c_157, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_117, c_154])).
% 1.96/1.27  tff(c_161, plain, (k4_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_157])).
% 1.96/1.27  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_161])).
% 1.96/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  Inference rules
% 1.96/1.27  ----------------------
% 1.96/1.27  #Ref     : 0
% 1.96/1.27  #Sup     : 66
% 1.96/1.27  #Fact    : 0
% 1.96/1.27  #Define  : 0
% 1.96/1.27  #Split   : 1
% 1.96/1.27  #Chain   : 0
% 1.96/1.27  #Close   : 0
% 1.96/1.27  
% 1.96/1.27  Ordering : KBO
% 1.96/1.27  
% 1.96/1.27  Simplification rules
% 1.96/1.27  ----------------------
% 1.96/1.27  #Subsume      : 12
% 1.96/1.27  #Demod        : 31
% 1.96/1.27  #Tautology    : 43
% 1.96/1.27  #SimpNegUnit  : 0
% 1.96/1.27  #BackRed      : 7
% 1.96/1.27  
% 1.96/1.27  #Partial instantiations: 0
% 1.96/1.27  #Strategies tried      : 1
% 1.96/1.27  
% 1.96/1.27  Timing (in seconds)
% 1.96/1.27  ----------------------
% 1.96/1.27  Preprocessing        : 0.30
% 1.96/1.27  Parsing              : 0.16
% 1.96/1.27  CNF conversion       : 0.02
% 1.96/1.27  Main loop            : 0.16
% 1.96/1.27  Inferencing          : 0.06
% 1.96/1.27  Reduction            : 0.06
% 1.96/1.27  Demodulation         : 0.04
% 1.96/1.27  BG Simplification    : 0.01
% 1.96/1.27  Subsumption          : 0.02
% 1.96/1.27  Abstraction          : 0.01
% 1.96/1.27  MUC search           : 0.00
% 1.96/1.27  Cooper               : 0.00
% 1.96/1.27  Total                : 0.48
% 1.96/1.27  Index Insertion      : 0.00
% 1.96/1.27  Index Deletion       : 0.00
% 1.96/1.27  Index Matching       : 0.00
% 1.96/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
