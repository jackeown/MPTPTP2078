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
% DateTime   : Thu Dec  3 09:55:58 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  48 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_51])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(k4_xboole_0(A_3,B_4),C_5)
      | ~ r1_tarski(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [C_23] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_23)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4])).

tff(c_10,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_75,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,k2_xboole_0(B_21,C_22))
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [C_25] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_2',C_25))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_75])).

tff(c_102,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_105,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.13  
% 1.72/1.13  %Foreground sorts:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Background operators:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Foreground operators:
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.72/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.13  
% 1.72/1.14  tff(f_49, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 1.72/1.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.72/1.14  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.72/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.72/1.14  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.72/1.14  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.14  tff(c_51, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.14  tff(c_58, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_51])).
% 1.72/1.14  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(k4_xboole_0(A_3, B_4), C_5) | ~r1_tarski(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.14  tff(c_86, plain, (![C_23]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_23) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_23)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_4])).
% 1.72/1.14  tff(c_10, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.14  tff(c_90, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_10])).
% 1.72/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.14  tff(c_12, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.14  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.14  tff(c_59, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.72/1.14  tff(c_75, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, k2_xboole_0(B_21, C_22)) | ~r1_tarski(k4_xboole_0(A_20, B_21), C_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.14  tff(c_96, plain, (![C_25]: (r1_tarski('#skF_1', k2_xboole_0('#skF_2', C_25)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), C_25))), inference(superposition, [status(thm), theory('equality')], [c_59, c_75])).
% 1.72/1.14  tff(c_102, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_96])).
% 1.72/1.14  tff(c_105, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_102])).
% 1.72/1.14  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_105])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 23
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 0
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 0
% 1.72/1.14  #Demod        : 1
% 1.72/1.14  #Tautology    : 15
% 1.72/1.14  #SimpNegUnit  : 1
% 1.72/1.14  #BackRed      : 0
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.28
% 1.72/1.14  Parsing              : 0.15
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.12
% 1.72/1.14  Inferencing          : 0.05
% 1.72/1.14  Reduction            : 0.04
% 1.72/1.14  Demodulation         : 0.03
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.02
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.14  Cooper               : 0.00
% 1.72/1.14  Total                : 0.42
% 1.72/1.14  Index Insertion      : 0.00
% 1.72/1.14  Index Deletion       : 0.00
% 1.72/1.14  Index Matching       : 0.00
% 1.72/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
