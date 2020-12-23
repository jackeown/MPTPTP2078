%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    ! [A_19,B_20,C_21] :
      ( k9_subset_1(A_19,B_20,C_21) = k3_xboole_0(B_20,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_22] : k9_subset_1('#skF_1',B_22,'#skF_3') = k3_xboole_0(B_22,'#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_22] :
      ( m1_subset_1(k3_xboole_0(B_22,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_42,plain,(
    ! [B_22] : m1_subset_1(k3_xboole_0(B_22,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k3_subset_1(A_34,C_35),k3_subset_1(A_34,B_36))
      | ~ r1_tarski(B_36,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,(
    ! [B_20] : k9_subset_1('#skF_1',B_20,'#skF_3') = k3_xboole_0(B_20,'#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_12,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_29,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_12])).

tff(c_105,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_29])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16,c_2,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.20  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.20  
% 1.79/1.20  %Foreground sorts:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Background operators:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Foreground operators:
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.79/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.20  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.79/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.20  
% 1.79/1.21  tff(f_52, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 1.79/1.21  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.79/1.21  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.79/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.79/1.21  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 1.79/1.21  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.21  tff(c_19, plain, (![A_19, B_20, C_21]: (k9_subset_1(A_19, B_20, C_21)=k3_xboole_0(B_20, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.21  tff(c_30, plain, (![B_22]: (k9_subset_1('#skF_1', B_22, '#skF_3')=k3_xboole_0(B_22, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.79/1.21  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.21  tff(c_36, plain, (![B_22]: (m1_subset_1(k3_xboole_0(B_22, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4])).
% 1.79/1.21  tff(c_42, plain, (![B_22]: (m1_subset_1(k3_xboole_0(B_22, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 1.79/1.21  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.21  tff(c_102, plain, (![A_34, C_35, B_36]: (r1_tarski(k3_subset_1(A_34, C_35), k3_subset_1(A_34, B_36)) | ~r1_tarski(B_36, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.21  tff(c_27, plain, (![B_20]: (k9_subset_1('#skF_1', B_20, '#skF_3')=k3_xboole_0(B_20, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.79/1.21  tff(c_12, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.21  tff(c_29, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_12])).
% 1.79/1.21  tff(c_105, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_29])).
% 1.79/1.21  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_16, c_2, c_105])).
% 1.79/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  Inference rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Ref     : 0
% 1.79/1.21  #Sup     : 20
% 1.79/1.21  #Fact    : 0
% 1.79/1.21  #Define  : 0
% 1.79/1.21  #Split   : 0
% 1.79/1.21  #Chain   : 0
% 1.79/1.21  #Close   : 0
% 1.79/1.21  
% 1.79/1.21  Ordering : KBO
% 1.79/1.21  
% 1.79/1.21  Simplification rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Subsume      : 0
% 1.79/1.21  #Demod        : 8
% 1.79/1.21  #Tautology    : 8
% 1.79/1.21  #SimpNegUnit  : 0
% 1.79/1.21  #BackRed      : 1
% 1.79/1.21  
% 1.79/1.21  #Partial instantiations: 0
% 1.79/1.21  #Strategies tried      : 1
% 1.79/1.21  
% 1.79/1.21  Timing (in seconds)
% 1.79/1.21  ----------------------
% 1.79/1.21  Preprocessing        : 0.29
% 1.79/1.21  Parsing              : 0.16
% 1.79/1.21  CNF conversion       : 0.02
% 1.79/1.21  Main loop            : 0.11
% 1.79/1.21  Inferencing          : 0.05
% 1.79/1.21  Reduction            : 0.03
% 1.79/1.21  Demodulation         : 0.03
% 1.79/1.21  BG Simplification    : 0.01
% 1.79/1.21  Subsumption          : 0.01
% 1.79/1.21  Abstraction          : 0.01
% 1.79/1.21  MUC search           : 0.00
% 1.79/1.21  Cooper               : 0.00
% 1.79/1.21  Total                : 0.42
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
