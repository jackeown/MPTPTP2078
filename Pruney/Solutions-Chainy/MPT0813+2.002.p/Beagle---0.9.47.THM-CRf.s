%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  45 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k4_xboole_0('#skF_1','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_124])).

tff(c_159,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_159])).

tff(c_184,plain,(
    k2_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_175])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(k2_xboole_0(A_28,B_30),C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_246,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(k2_xboole_0(B_35,A_33),C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_286,plain,(
    ! [C_36] :
      ( r1_tarski('#skF_1',C_36)
      | ~ r1_tarski('#skF_4',C_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_246])).

tff(c_119,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_119,c_18])).

tff(c_294,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_286,c_123])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.24  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.24  
% 2.07/1.25  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.07/1.25  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.07/1.25  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.07/1.25  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.07/1.25  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.07/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.25  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.07/1.25  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.25  tff(c_142, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.25  tff(c_150, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_142])).
% 2.07/1.25  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.25  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.25  tff(c_124, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.25  tff(c_128, plain, (k4_xboole_0('#skF_1', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_124])).
% 2.07/1.25  tff(c_159, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.25  tff(c_175, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_128, c_159])).
% 2.07/1.25  tff(c_184, plain, (k2_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_175])).
% 2.07/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.25  tff(c_204, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(k2_xboole_0(A_28, B_30), C_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.25  tff(c_246, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(k2_xboole_0(B_35, A_33), C_34))), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 2.07/1.25  tff(c_286, plain, (![C_36]: (r1_tarski('#skF_1', C_36) | ~r1_tarski('#skF_4', C_36))), inference(superposition, [status(thm), theory('equality')], [c_184, c_246])).
% 2.07/1.25  tff(c_119, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.25  tff(c_18, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.25  tff(c_123, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_119, c_18])).
% 2.07/1.25  tff(c_294, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_286, c_123])).
% 2.07/1.25  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_294])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 71
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 5
% 2.07/1.25  #Demod        : 20
% 2.07/1.25  #Tautology    : 43
% 2.07/1.25  #SimpNegUnit  : 0
% 2.07/1.25  #BackRed      : 0
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.28
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.21
% 2.07/1.25  Inferencing          : 0.08
% 2.07/1.25  Reduction            : 0.07
% 2.07/1.25  Demodulation         : 0.05
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.03
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.52
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
