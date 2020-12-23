%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:29 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_26,B_27] : k2_xboole_0(k4_xboole_0(A_26,B_27),k4_xboole_0(B_27,A_26)) = k5_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),k5_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_88,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),k5_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_107,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k2_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_125,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_128,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_128])).

tff(c_133,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_137,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_133])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.96/1.24  
% 1.96/1.24  %Foreground sorts:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Background operators:
% 1.96/1.24  
% 1.96/1.24  
% 1.96/1.24  %Foreground operators:
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.24  
% 1.96/1.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.96/1.24  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.96/1.24  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.96/1.24  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.96/1.24  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.96/1.24  tff(f_48, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.96/1.24  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.24  tff(c_70, plain, (![A_26, B_27]: (k2_xboole_0(k4_xboole_0(A_26, B_27), k4_xboole_0(B_27, A_26))=k5_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.24  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.24  tff(c_82, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), k5_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 1.96/1.24  tff(c_88, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 1.96/1.24  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.24  tff(c_76, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), k5_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 1.96/1.24  tff(c_107, plain, (![A_36, C_37, B_38]: (r1_tarski(k2_xboole_0(A_36, C_37), B_38) | ~r1_tarski(C_37, B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.24  tff(c_16, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.24  tff(c_114, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_107, c_16])).
% 1.96/1.24  tff(c_125, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_114])).
% 1.96/1.24  tff(c_128, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_125])).
% 1.96/1.24  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_128])).
% 1.96/1.24  tff(c_133, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_114])).
% 1.96/1.24  tff(c_137, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_133])).
% 1.96/1.24  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_137])).
% 1.96/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.24  
% 1.96/1.24  Inference rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Ref     : 0
% 1.96/1.24  #Sup     : 28
% 1.96/1.24  #Fact    : 0
% 1.96/1.24  #Define  : 0
% 1.96/1.24  #Split   : 1
% 1.96/1.24  #Chain   : 0
% 1.96/1.24  #Close   : 0
% 1.96/1.24  
% 1.96/1.24  Ordering : KBO
% 1.96/1.24  
% 1.96/1.24  Simplification rules
% 1.96/1.24  ----------------------
% 1.96/1.24  #Subsume      : 2
% 1.96/1.24  #Demod        : 5
% 1.96/1.24  #Tautology    : 17
% 1.96/1.24  #SimpNegUnit  : 0
% 1.96/1.24  #BackRed      : 0
% 1.96/1.24  
% 1.96/1.24  #Partial instantiations: 0
% 1.96/1.24  #Strategies tried      : 1
% 1.96/1.24  
% 1.96/1.24  Timing (in seconds)
% 1.96/1.24  ----------------------
% 1.96/1.25  Preprocessing        : 0.29
% 1.96/1.25  Parsing              : 0.16
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.15
% 1.96/1.25  Inferencing          : 0.05
% 1.96/1.25  Reduction            : 0.05
% 1.96/1.25  Demodulation         : 0.05
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.02
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 1.96/1.25  Cooper               : 0.00
% 1.96/1.25  Total                : 0.46
% 1.96/1.25  Index Insertion      : 0.00
% 1.96/1.25  Index Deletion       : 0.00
% 1.96/1.25  Index Matching       : 0.00
% 1.96/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
