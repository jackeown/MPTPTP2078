%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_58,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),B_14)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_78,plain,(
    ! [B_17,A_18] :
      ( k3_xboole_0(B_17,k1_tarski(A_18)) = k1_tarski(A_18)
      | ~ r2_hidden(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_15])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:37:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.17  
% 1.79/1.18  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.79/1.18  tff(f_45, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.79/1.18  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.79/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.79/1.18  tff(c_58, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), B_14) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.18  tff(c_14, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.18  tff(c_62, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_14])).
% 1.79/1.18  tff(c_78, plain, (![B_17, A_18]: (k3_xboole_0(B_17, k1_tarski(A_18))=k1_tarski(A_18) | ~r2_hidden(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.18  tff(c_12, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.18  tff(c_15, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 1.79/1.18  tff(c_90, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_78, c_15])).
% 1.79/1.18  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_90])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 22
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 0
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.18  
% 1.79/1.18  Ordering : KBO
% 1.79/1.18  
% 1.79/1.18  Simplification rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Subsume      : 0
% 1.79/1.18  #Demod        : 2
% 1.79/1.18  #Tautology    : 13
% 1.79/1.18  #SimpNegUnit  : 0
% 1.79/1.18  #BackRed      : 0
% 1.79/1.18  
% 1.79/1.18  #Partial instantiations: 0
% 1.79/1.18  #Strategies tried      : 1
% 1.79/1.18  
% 1.79/1.18  Timing (in seconds)
% 1.79/1.18  ----------------------
% 1.79/1.18  Preprocessing        : 0.29
% 1.79/1.18  Parsing              : 0.15
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.10
% 1.79/1.18  Inferencing          : 0.04
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.01
% 1.79/1.18  Abstraction          : 0.01
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.41
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
