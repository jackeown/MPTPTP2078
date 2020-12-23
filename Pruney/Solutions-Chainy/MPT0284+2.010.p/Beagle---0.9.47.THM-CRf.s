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
% DateTime   : Thu Dec  3 09:53:28 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  47 expanded)
%              Number of equality atoms :    7 (   8 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_85,plain,(
    ! [A_32,B_33] : k2_xboole_0(k4_xboole_0(A_32,B_33),k4_xboole_0(B_33,A_32)) = k5_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [B_34,A_35] : k2_xboole_0(k4_xboole_0(B_34,A_35),k4_xboole_0(A_35,B_34)) = k5_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [B_36,A_37] : k5_xboole_0(B_36,A_37) = k5_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),k5_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    ! [B_36,A_37] : r1_tarski(k4_xboole_0(B_36,A_37),k5_xboole_0(A_37,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_10])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_zfmisc_1(A_16),k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(k2_xboole_0(A_42,C_43),B_44)
      | ~ r1_tarski(C_43,B_44)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_206,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_190,c_18])).

tff(c_210,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_213,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_213])).

tff(c_218,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_222,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_218])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.97/1.26  
% 1.97/1.26  %Foreground sorts:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Background operators:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Foreground operators:
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.26  
% 1.97/1.27  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.97/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.97/1.27  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.97/1.27  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.97/1.27  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.97/1.27  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.97/1.27  tff(c_85, plain, (![A_32, B_33]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k4_xboole_0(B_33, A_32))=k5_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.27  tff(c_106, plain, (![B_34, A_35]: (k2_xboole_0(k4_xboole_0(B_34, A_35), k4_xboole_0(A_35, B_34))=k5_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2])).
% 1.97/1.27  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.27  tff(c_137, plain, (![B_36, A_37]: (k5_xboole_0(B_36, A_37)=k5_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4])).
% 1.97/1.27  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), k5_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.27  tff(c_155, plain, (![B_36, A_37]: (r1_tarski(k4_xboole_0(B_36, A_37), k5_xboole_0(A_37, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_10])).
% 1.97/1.27  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k1_zfmisc_1(A_16), k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.27  tff(c_190, plain, (![A_42, C_43, B_44]: (r1_tarski(k2_xboole_0(A_42, C_43), B_44) | ~r1_tarski(C_43, B_44) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.27  tff(c_18, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.27  tff(c_206, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_190, c_18])).
% 1.97/1.27  tff(c_210, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_206])).
% 1.97/1.27  tff(c_213, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_210])).
% 1.97/1.27  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_213])).
% 1.97/1.27  tff(c_218, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_206])).
% 1.97/1.27  tff(c_222, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_218])).
% 1.97/1.27  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_222])).
% 1.97/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  Inference rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Ref     : 0
% 1.97/1.27  #Sup     : 49
% 1.97/1.27  #Fact    : 0
% 1.97/1.27  #Define  : 0
% 1.97/1.27  #Split   : 1
% 1.97/1.27  #Chain   : 0
% 1.97/1.27  #Close   : 0
% 1.97/1.27  
% 1.97/1.27  Ordering : KBO
% 1.97/1.27  
% 1.97/1.27  Simplification rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Subsume      : 3
% 1.97/1.27  #Demod        : 12
% 1.97/1.27  #Tautology    : 36
% 1.97/1.27  #SimpNegUnit  : 0
% 1.97/1.27  #BackRed      : 0
% 1.97/1.27  
% 1.97/1.27  #Partial instantiations: 0
% 1.97/1.27  #Strategies tried      : 1
% 1.97/1.27  
% 1.97/1.27  Timing (in seconds)
% 1.97/1.27  ----------------------
% 1.97/1.27  Preprocessing        : 0.31
% 1.97/1.27  Parsing              : 0.16
% 1.97/1.27  CNF conversion       : 0.02
% 1.97/1.27  Main loop            : 0.16
% 1.97/1.27  Inferencing          : 0.06
% 1.97/1.27  Reduction            : 0.06
% 1.97/1.27  Demodulation         : 0.05
% 1.97/1.27  BG Simplification    : 0.01
% 1.97/1.27  Subsumption          : 0.02
% 1.97/1.27  Abstraction          : 0.01
% 1.97/1.27  MUC search           : 0.00
% 1.97/1.27  Cooper               : 0.00
% 1.97/1.27  Total                : 0.49
% 1.97/1.27  Index Insertion      : 0.00
% 1.97/1.27  Index Deletion       : 0.00
% 1.97/1.27  Index Matching       : 0.00
% 1.97/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
