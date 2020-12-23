%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:28 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_97,plain,(
    ! [A_32,B_33] : k2_xboole_0(k4_xboole_0(A_32,B_33),k4_xboole_0(B_33,A_32)) = k5_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_20,A_21] : k2_xboole_0(B_20,A_21) = k2_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_21,B_20] : r1_tarski(A_21,k2_xboole_0(B_20,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_103,plain,(
    ! [B_33,A_32] : r1_tarski(k4_xboole_0(B_33,A_32),k5_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_35])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_zfmisc_1(A_16),k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [A_32,B_33] : r1_tarski(k4_xboole_0(A_32,B_33),k5_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_173,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(k2_xboole_0(A_44,C_45),B_46)
      | ~ r1_tarski(C_45,B_46)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_189,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_173,c_18])).

tff(c_240,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_243,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_243])).

tff(c_248,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_252,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_248])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:21:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.28  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.93/1.28  
% 1.93/1.28  %Foreground sorts:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Background operators:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Foreground operators:
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.28  
% 1.93/1.29  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.93/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.93/1.29  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.93/1.29  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.93/1.29  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.93/1.29  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.93/1.29  tff(c_97, plain, (![A_32, B_33]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k4_xboole_0(B_33, A_32))=k5_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.29  tff(c_20, plain, (![B_20, A_21]: (k2_xboole_0(B_20, A_21)=k2_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.29  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.29  tff(c_35, plain, (![A_21, B_20]: (r1_tarski(A_21, k2_xboole_0(B_20, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_8])).
% 1.93/1.29  tff(c_103, plain, (![B_33, A_32]: (r1_tarski(k4_xboole_0(B_33, A_32), k5_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_35])).
% 1.93/1.29  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k1_zfmisc_1(A_16), k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.29  tff(c_112, plain, (![A_32, B_33]: (r1_tarski(k4_xboole_0(A_32, B_33), k5_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 1.93/1.29  tff(c_173, plain, (![A_44, C_45, B_46]: (r1_tarski(k2_xboole_0(A_44, C_45), B_46) | ~r1_tarski(C_45, B_46) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.29  tff(c_18, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.29  tff(c_189, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_173, c_18])).
% 1.93/1.29  tff(c_240, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_189])).
% 1.93/1.29  tff(c_243, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_240])).
% 1.93/1.29  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_243])).
% 1.93/1.29  tff(c_248, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_189])).
% 1.93/1.29  tff(c_252, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_248])).
% 1.93/1.29  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_252])).
% 1.93/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  Inference rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Ref     : 0
% 1.93/1.29  #Sup     : 57
% 1.93/1.29  #Fact    : 0
% 1.93/1.29  #Define  : 0
% 1.93/1.29  #Split   : 1
% 1.93/1.29  #Chain   : 0
% 1.93/1.29  #Close   : 0
% 1.93/1.29  
% 1.93/1.29  Ordering : KBO
% 1.93/1.29  
% 1.93/1.29  Simplification rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Subsume      : 3
% 1.93/1.29  #Demod        : 16
% 1.93/1.29  #Tautology    : 40
% 1.93/1.29  #SimpNegUnit  : 0
% 1.93/1.29  #BackRed      : 0
% 1.93/1.29  
% 1.93/1.29  #Partial instantiations: 0
% 1.93/1.29  #Strategies tried      : 1
% 1.93/1.29  
% 1.93/1.29  Timing (in seconds)
% 1.93/1.29  ----------------------
% 1.93/1.29  Preprocessing        : 0.31
% 1.93/1.29  Parsing              : 0.16
% 1.93/1.29  CNF conversion       : 0.02
% 1.93/1.29  Main loop            : 0.17
% 1.93/1.29  Inferencing          : 0.06
% 1.93/1.29  Reduction            : 0.06
% 1.93/1.30  Demodulation         : 0.05
% 1.93/1.30  BG Simplification    : 0.01
% 1.93/1.30  Subsumption          : 0.02
% 1.93/1.30  Abstraction          : 0.01
% 1.93/1.30  MUC search           : 0.00
% 1.93/1.30  Cooper               : 0.00
% 1.93/1.30  Total                : 0.51
% 1.93/1.30  Index Insertion      : 0.00
% 1.93/1.30  Index Deletion       : 0.00
% 1.93/1.30  Index Matching       : 0.00
% 1.93/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
