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
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_64,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    k2_xboole_0('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_18,C_19,B_20] :
      ( r1_tarski(A_18,k2_xboole_0(C_19,B_20))
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_18,A_1,B_2] :
      ( r1_tarski(A_18,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_18,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_141,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_25,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_111])).

tff(c_55,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_55,c_12])).

tff(c_147,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_63])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.13  
% 1.63/1.14  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 1.63/1.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.63/1.14  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.63/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.63/1.14  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.63/1.14  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.14  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.14  tff(c_50, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.14  tff(c_54, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.63/1.14  tff(c_64, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.14  tff(c_71, plain, (k2_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_64])).
% 1.63/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.14  tff(c_96, plain, (![A_18, C_19, B_20]: (r1_tarski(A_18, k2_xboole_0(C_19, B_20)) | ~r1_tarski(A_18, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.14  tff(c_111, plain, (![A_18, A_1, B_2]: (r1_tarski(A_18, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_18, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96])).
% 1.63/1.14  tff(c_141, plain, (![A_25]: (r1_tarski(A_25, k2_zfmisc_1('#skF_2', '#skF_3')) | ~r1_tarski(A_25, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_111])).
% 1.63/1.14  tff(c_55, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.14  tff(c_12, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.14  tff(c_63, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_55, c_12])).
% 1.63/1.14  tff(c_147, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_141, c_63])).
% 1.63/1.14  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_147])).
% 1.63/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  Inference rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Ref     : 0
% 1.63/1.14  #Sup     : 37
% 1.63/1.14  #Fact    : 0
% 1.63/1.14  #Define  : 0
% 1.63/1.14  #Split   : 0
% 1.63/1.14  #Chain   : 0
% 1.63/1.14  #Close   : 0
% 1.63/1.14  
% 1.63/1.14  Ordering : KBO
% 1.63/1.14  
% 1.63/1.14  Simplification rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Subsume      : 4
% 1.63/1.14  #Demod        : 4
% 1.63/1.14  #Tautology    : 21
% 1.63/1.14  #SimpNegUnit  : 0
% 1.63/1.14  #BackRed      : 0
% 1.63/1.14  
% 1.63/1.14  #Partial instantiations: 0
% 1.63/1.14  #Strategies tried      : 1
% 1.63/1.14  
% 1.63/1.14  Timing (in seconds)
% 1.63/1.14  ----------------------
% 1.63/1.14  Preprocessing        : 0.25
% 1.63/1.14  Parsing              : 0.14
% 1.63/1.14  CNF conversion       : 0.02
% 1.63/1.14  Main loop            : 0.14
% 1.63/1.14  Inferencing          : 0.06
% 1.63/1.14  Reduction            : 0.04
% 1.63/1.14  Demodulation         : 0.03
% 1.63/1.14  BG Simplification    : 0.01
% 1.63/1.14  Subsumption          : 0.02
% 1.63/1.14  Abstraction          : 0.01
% 1.63/1.14  MUC search           : 0.00
% 1.63/1.14  Cooper               : 0.00
% 1.63/1.14  Total                : 0.41
% 1.63/1.14  Index Insertion      : 0.00
% 1.63/1.14  Index Deletion       : 0.00
% 1.63/1.14  Index Matching       : 0.00
% 1.63/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
