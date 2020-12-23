%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  79 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_29,B_30,C_31] :
      ( k4_subset_1(A_29,B_30,C_31) = k2_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [B_32] :
      ( k4_subset_1('#skF_1',B_32,'#skF_3') = k2_xboole_0(B_32,'#skF_3')
      | ~ m1_subset_1(B_32,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_137])).

tff(c_152,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_144])).

tff(c_12,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_12])).

tff(c_211,plain,(
    ! [A_38,B_39,C_40] :
      ( m1_subset_1(k4_subset_1(A_38,B_39,C_40),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_233,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_211])).

tff(c_246,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_233])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_293,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_246,c_6])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_34,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k4_xboole_0(A_19,B_20),C_21) = k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_22,B_23,C_24] : r1_tarski(k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)),k4_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_70,plain,(
    ! [C_24] : r1_tarski(k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_24)),k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_67])).

tff(c_474,plain,(
    r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_70])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.17/1.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.29  
% 2.17/1.30  tff(f_53, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.17/1.30  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.17/1.30  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.17/1.30  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.17/1.30  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.17/1.30  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.17/1.30  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.30  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.30  tff(c_137, plain, (![A_29, B_30, C_31]: (k4_subset_1(A_29, B_30, C_31)=k2_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.30  tff(c_144, plain, (![B_32]: (k4_subset_1('#skF_1', B_32, '#skF_3')=k2_xboole_0(B_32, '#skF_3') | ~m1_subset_1(B_32, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_137])).
% 2.17/1.30  tff(c_152, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_144])).
% 2.17/1.30  tff(c_12, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.30  tff(c_157, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_12])).
% 2.17/1.30  tff(c_211, plain, (![A_38, B_39, C_40]: (m1_subset_1(k4_subset_1(A_38, B_39, C_40), k1_zfmisc_1(A_38)) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.30  tff(c_233, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_211])).
% 2.17/1.30  tff(c_246, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_233])).
% 2.17/1.30  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_293, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_246, c_6])).
% 2.17/1.30  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_26, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.17/1.30  tff(c_34, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k4_xboole_0(A_19, B_20), C_21)=k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.30  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.30  tff(c_67, plain, (![A_22, B_23, C_24]: (r1_tarski(k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)), k4_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2])).
% 2.17/1.30  tff(c_70, plain, (![C_24]: (r1_tarski(k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_24)), k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_67])).
% 2.17/1.30  tff(c_474, plain, (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_70])).
% 2.17/1.30  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_474])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 127
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 0
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 0
% 2.17/1.30  #Demod        : 58
% 2.17/1.30  #Tautology    : 36
% 2.17/1.30  #SimpNegUnit  : 1
% 2.17/1.30  #BackRed      : 1
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.27
% 2.17/1.30  Parsing              : 0.15
% 2.17/1.30  CNF conversion       : 0.01
% 2.17/1.30  Main loop            : 0.27
% 2.17/1.30  Inferencing          : 0.09
% 2.17/1.30  Reduction            : 0.10
% 2.17/1.31  Demodulation         : 0.07
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.04
% 2.17/1.31  Abstraction          : 0.02
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.56
% 2.53/1.31  Index Insertion      : 0.00
% 2.53/1.31  Index Deletion       : 0.00
% 2.53/1.31  Index Matching       : 0.00
% 2.53/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
