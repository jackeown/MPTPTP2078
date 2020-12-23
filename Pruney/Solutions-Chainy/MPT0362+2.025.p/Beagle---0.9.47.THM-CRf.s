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
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  60 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_26,B_27,C_28] :
      ( k9_subset_1(A_26,B_27,C_28) = k3_xboole_0(B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [B_27] : k9_subset_1('#skF_1',B_27,'#skF_3') = k3_xboole_0(B_27,'#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_78])).

tff(c_106,plain,(
    ! [A_31,B_32,C_33] :
      ( m1_subset_1(k9_subset_1(A_31,B_32,C_33),k1_zfmisc_1(A_31))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [B_27] :
      ( m1_subset_1(k3_xboole_0(B_27,'#skF_3'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_106])).

tff(c_132,plain,(
    ! [B_35] : m1_subset_1(k3_xboole_0(B_35,'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [B_36] : k4_xboole_0('#skF_1',k3_xboole_0(B_36,'#skF_3')) = k3_subset_1('#skF_1',k3_xboole_0(B_36,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( r1_tarski(k4_xboole_0(C_5,B_4),k4_xboole_0(C_5,A_3))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_3] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_1',A_3))
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_290,plain,(
    ! [B_51] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0(B_51,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_51,'#skF_3'),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_41])).

tff(c_12,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k9_subset_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_293,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_290,c_85])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 12:45:14 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.15/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.24  
% 2.15/1.25  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.15/1.25  tff(f_51, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.15/1.25  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.15/1.25  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.15/1.25  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.15/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.15/1.25  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.25  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.25  tff(c_78, plain, (![A_26, B_27, C_28]: (k9_subset_1(A_26, B_27, C_28)=k3_xboole_0(B_27, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.15/1.25  tff(c_83, plain, (![B_27]: (k9_subset_1('#skF_1', B_27, '#skF_3')=k3_xboole_0(B_27, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_78])).
% 2.15/1.25  tff(c_106, plain, (![A_31, B_32, C_33]: (m1_subset_1(k9_subset_1(A_31, B_32, C_33), k1_zfmisc_1(A_31)) | ~m1_subset_1(C_33, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.25  tff(c_117, plain, (![B_27]: (m1_subset_1(k3_xboole_0(B_27, '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_83, c_106])).
% 2.15/1.25  tff(c_132, plain, (![B_35]: (m1_subset_1(k3_xboole_0(B_35, '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 2.15/1.25  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.25  tff(c_140, plain, (![B_36]: (k4_xboole_0('#skF_1', k3_xboole_0(B_36, '#skF_3'))=k3_subset_1('#skF_1', k3_xboole_0(B_36, '#skF_3')))), inference(resolution, [status(thm)], [c_132, c_6])).
% 2.15/1.25  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.25  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.25  tff(c_26, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_18])).
% 2.15/1.25  tff(c_4, plain, (![C_5, B_4, A_3]: (r1_tarski(k4_xboole_0(C_5, B_4), k4_xboole_0(C_5, A_3)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.25  tff(c_41, plain, (![A_3]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', A_3)) | ~r1_tarski(A_3, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 2.15/1.25  tff(c_290, plain, (![B_51]: (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0(B_51, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_51, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_41])).
% 2.15/1.25  tff(c_12, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k9_subset_1('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.25  tff(c_85, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_12])).
% 2.15/1.25  tff(c_293, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_290, c_85])).
% 2.15/1.25  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_293])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 74
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 4
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 4
% 2.15/1.25  #Demod        : 14
% 2.15/1.25  #Tautology    : 20
% 2.15/1.25  #SimpNegUnit  : 0
% 2.15/1.25  #BackRed      : 1
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.25  Preprocessing        : 0.27
% 2.15/1.25  Parsing              : 0.15
% 2.15/1.25  CNF conversion       : 0.02
% 2.15/1.25  Main loop            : 0.22
% 2.15/1.25  Inferencing          : 0.09
% 2.15/1.25  Reduction            : 0.07
% 2.15/1.25  Demodulation         : 0.05
% 2.15/1.25  BG Simplification    : 0.01
% 2.15/1.25  Subsumption          : 0.04
% 2.15/1.25  Abstraction          : 0.01
% 2.15/1.25  MUC search           : 0.00
% 2.15/1.25  Cooper               : 0.00
% 2.15/1.25  Total                : 0.52
% 2.15/1.25  Index Insertion      : 0.00
% 2.15/1.25  Index Deletion       : 0.00
% 2.15/1.25  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
