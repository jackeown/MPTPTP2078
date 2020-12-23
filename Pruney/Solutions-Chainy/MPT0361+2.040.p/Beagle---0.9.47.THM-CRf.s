%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  75 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    ! [A_19,B_20,C_21] :
      ( k4_subset_1(A_19,B_20,C_21) = k2_xboole_0(B_20,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    ! [B_22] :
      ( k4_subset_1('#skF_1',B_22,'#skF_3') = k2_xboole_0(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_42,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k4_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_67,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_63])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(k3_subset_1(A_27,C_28),k3_subset_1(A_27,B_29))
      | ~ r1_tarski(B_29,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_214,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_208,c_59])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_67,c_2,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:23:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.95/1.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.20  
% 1.95/1.21  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 1.95/1.21  tff(f_39, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.95/1.21  tff(f_33, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 1.95/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.95/1.21  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 1.95/1.21  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.21  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.21  tff(c_19, plain, (![A_19, B_20, C_21]: (k4_subset_1(A_19, B_20, C_21)=k2_xboole_0(B_20, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.21  tff(c_29, plain, (![B_22]: (k4_subset_1('#skF_1', B_22, '#skF_3')=k2_xboole_0(B_22, '#skF_3') | ~m1_subset_1(B_22, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.95/1.21  tff(c_42, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_29])).
% 1.95/1.21  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k4_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.21  tff(c_63, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 1.95/1.21  tff(c_67, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_63])).
% 1.95/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.21  tff(c_208, plain, (![A_27, C_28, B_29]: (r1_tarski(k3_subset_1(A_27, C_28), k3_subset_1(A_27, B_29)) | ~r1_tarski(B_29, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(A_27)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.95/1.21  tff(c_12, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.21  tff(c_59, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 1.95/1.21  tff(c_214, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_208, c_59])).
% 1.95/1.21  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_67, c_2, c_214])).
% 1.95/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  Inference rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Ref     : 0
% 1.95/1.21  #Sup     : 56
% 1.95/1.21  #Fact    : 0
% 1.95/1.21  #Define  : 0
% 1.95/1.21  #Split   : 0
% 1.95/1.21  #Chain   : 0
% 1.95/1.21  #Close   : 0
% 1.95/1.21  
% 1.95/1.21  Ordering : KBO
% 1.95/1.21  
% 1.95/1.21  Simplification rules
% 1.95/1.21  ----------------------
% 1.95/1.21  #Subsume      : 0
% 1.95/1.21  #Demod        : 20
% 1.95/1.21  #Tautology    : 17
% 1.95/1.21  #SimpNegUnit  : 0
% 1.95/1.21  #BackRed      : 1
% 1.95/1.21  
% 1.95/1.21  #Partial instantiations: 0
% 1.95/1.21  #Strategies tried      : 1
% 1.95/1.21  
% 1.95/1.21  Timing (in seconds)
% 1.95/1.21  ----------------------
% 1.95/1.22  Preprocessing        : 0.28
% 1.95/1.22  Parsing              : 0.15
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.18
% 1.95/1.22  Inferencing          : 0.06
% 1.95/1.22  Reduction            : 0.06
% 1.95/1.22  Demodulation         : 0.04
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.04
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.49
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
