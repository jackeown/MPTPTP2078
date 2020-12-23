%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:29 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 135 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   27 ( 156 expanded)
%              Number of equality atoms :   26 ( 155 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_51,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( k1_xboole_0 = A_15
      | k2_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_32])).

tff(c_37,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_66,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_37])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_93,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_51])).

tff(c_122,plain,(
    k2_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_108,c_93])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6])).

tff(c_139,plain,(
    k4_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_132])).

tff(c_112,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_36])).

tff(c_148,plain,(
    ! [B_21] : k4_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) != k1_tarski(B_21) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_148])).

tff(c_155,plain,(
    k4_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_151])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  %$ k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.65/1.12  tff(f_48, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.65/1.12  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.65/1.12  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.65/1.12  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.65/1.12  tff(c_51, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.12  tff(c_18, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.12  tff(c_32, plain, (![A_15, B_16]: (k1_xboole_0=A_15 | k2_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.12  tff(c_36, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_32])).
% 1.65/1.12  tff(c_37, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 1.65/1.12  tff(c_66, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_51, c_37])).
% 1.65/1.12  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.12  tff(c_108, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 1.65/1.12  tff(c_93, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37, c_51])).
% 1.65/1.12  tff(c_122, plain, (k2_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_108, c_93])).
% 1.65/1.12  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.12  tff(c_132, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k2_xboole_0(A_19, B_20))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6])).
% 1.65/1.12  tff(c_139, plain, (k4_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_122, c_132])).
% 1.65/1.12  tff(c_112, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_36])).
% 1.65/1.12  tff(c_148, plain, (![B_21]: (k4_xboole_0(k1_tarski(B_21), k1_tarski(B_21))!=k1_tarski(B_21))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.12  tff(c_151, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_112, c_148])).
% 1.65/1.12  tff(c_155, plain, (k4_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_151])).
% 1.65/1.12  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_155])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 42
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 24
% 1.65/1.12  #Tautology    : 33
% 1.65/1.12  #SimpNegUnit  : 0
% 1.65/1.12  #BackRed      : 5
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.12  Preprocessing        : 0.27
% 1.65/1.12  Parsing              : 0.14
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.11
% 1.65/1.12  Inferencing          : 0.04
% 1.65/1.12  Reduction            : 0.04
% 1.65/1.12  Demodulation         : 0.04
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.02
% 1.65/1.12  Abstraction          : 0.01
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.41
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
