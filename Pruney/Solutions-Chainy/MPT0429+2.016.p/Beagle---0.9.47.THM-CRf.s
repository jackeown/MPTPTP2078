%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_setfam_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B = k1_tarski(A)
       => k7_setfam_1(A,B) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_8,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_22] :
      ( k7_setfam_1(A_22,k1_tarski(A_22)) = k1_tarski(k1_xboole_0)
      | ~ m1_subset_1(k1_tarski(A_22),k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [A_22] :
      ( k7_setfam_1(A_22,k1_tarski(A_22)) = k1_tarski(k1_xboole_0)
      | ~ r1_tarski(k1_tarski(A_22),k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_88,plain,(
    ! [A_23] : k7_setfam_1(A_23,k1_tarski(A_23)) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_56,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k7_setfam_1(A_15,B_16),k1_zfmisc_1(k1_zfmisc_1(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k7_setfam_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(resolution,[status(thm)],[c_56,c_12])).

tff(c_106,plain,(
    ! [A_24] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(k1_tarski(A_24),k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_63])).

tff(c_109,plain,(
    ! [A_24] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_24))
      | ~ r1_tarski(k1_tarski(A_24),k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_115,plain,(
    ! [A_24] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_109])).

tff(c_40,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_18])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  %$ r1_tarski > m1_subset_1 > k7_setfam_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.13  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.71/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.13  
% 1.71/1.14  tff(f_31, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.71/1.14  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.71/1.14  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((B = k1_tarski(A)) => (k7_setfam_1(A, B) = k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_setfam_1)).
% 1.71/1.14  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 1.71/1.14  tff(f_48, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.71/1.14  tff(c_8, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.14  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.14  tff(c_77, plain, (![A_22]: (k7_setfam_1(A_22, k1_tarski(A_22))=k1_tarski(k1_xboole_0) | ~m1_subset_1(k1_tarski(A_22), k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.14  tff(c_80, plain, (![A_22]: (k7_setfam_1(A_22, k1_tarski(A_22))=k1_tarski(k1_xboole_0) | ~r1_tarski(k1_tarski(A_22), k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_14, c_77])).
% 1.71/1.14  tff(c_88, plain, (![A_23]: (k7_setfam_1(A_23, k1_tarski(A_23))=k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 1.71/1.14  tff(c_56, plain, (![A_15, B_16]: (m1_subset_1(k7_setfam_1(A_15, B_16), k1_zfmisc_1(k1_zfmisc_1(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.14  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.14  tff(c_63, plain, (![A_15, B_16]: (r1_tarski(k7_setfam_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(resolution, [status(thm)], [c_56, c_12])).
% 1.71/1.14  tff(c_106, plain, (![A_24]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_24)) | ~m1_subset_1(k1_tarski(A_24), k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_63])).
% 1.71/1.14  tff(c_109, plain, (![A_24]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_24)) | ~r1_tarski(k1_tarski(A_24), k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_14, c_106])).
% 1.71/1.14  tff(c_115, plain, (![A_24]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_109])).
% 1.71/1.14  tff(c_40, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.14  tff(c_18, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.14  tff(c_47, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_18])).
% 1.71/1.14  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_47])).
% 1.71/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  Inference rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Ref     : 0
% 1.71/1.14  #Sup     : 24
% 1.71/1.14  #Fact    : 0
% 1.71/1.14  #Define  : 0
% 1.71/1.14  #Split   : 0
% 1.71/1.14  #Chain   : 0
% 1.71/1.14  #Close   : 0
% 1.71/1.14  
% 1.71/1.14  Ordering : KBO
% 1.71/1.14  
% 1.71/1.14  Simplification rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Subsume      : 0
% 1.71/1.14  #Demod        : 10
% 1.71/1.14  #Tautology    : 14
% 1.71/1.14  #SimpNegUnit  : 0
% 1.71/1.14  #BackRed      : 1
% 1.71/1.14  
% 1.71/1.14  #Partial instantiations: 0
% 1.71/1.14  #Strategies tried      : 1
% 1.71/1.14  
% 1.71/1.14  Timing (in seconds)
% 1.71/1.14  ----------------------
% 1.71/1.14  Preprocessing        : 0.28
% 1.71/1.14  Parsing              : 0.15
% 1.71/1.14  CNF conversion       : 0.01
% 1.71/1.14  Main loop            : 0.12
% 1.71/1.14  Inferencing          : 0.04
% 1.71/1.14  Reduction            : 0.03
% 1.71/1.14  Demodulation         : 0.03
% 1.71/1.14  BG Simplification    : 0.01
% 1.71/1.14  Subsumption          : 0.02
% 1.71/1.14  Abstraction          : 0.01
% 1.71/1.14  MUC search           : 0.00
% 1.71/1.14  Cooper               : 0.00
% 1.71/1.14  Total                : 0.42
% 1.71/1.14  Index Insertion      : 0.00
% 1.71/1.14  Index Deletion       : 0.00
% 1.71/1.14  Index Matching       : 0.00
% 1.71/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
