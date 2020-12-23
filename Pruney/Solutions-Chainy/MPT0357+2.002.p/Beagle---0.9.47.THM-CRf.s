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
% DateTime   : Thu Dec  3 09:55:58 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  54 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_152])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(k4_xboole_0(A_3,B_4),C_5)
      | ~ r1_tarski(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [C_38] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_38)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_4])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_181,c_16])).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [B_24,A_25] : k3_tarski(k2_tarski(B_24,A_25)) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_18,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_152])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k2_xboole_0(B_7,C_8))
      | ~ r1_tarski(k4_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [C_41] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_2',C_41))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_6])).

tff(c_198,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_201,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_198])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  %$ r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.28  
% 2.11/1.28  %Foreground sorts:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Background operators:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Foreground operators:
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.11/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.28  
% 2.11/1.30  tff(f_55, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 2.11/1.30  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.11/1.30  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.11/1.30  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.30  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.11/1.30  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.30  tff(c_152, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.30  tff(c_159, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_152])).
% 2.11/1.30  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(k4_xboole_0(A_3, B_4), C_5) | ~r1_tarski(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.30  tff(c_181, plain, (![C_38]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_38) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_38)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_4])).
% 2.11/1.30  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.30  tff(c_185, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_16])).
% 2.11/1.30  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.30  tff(c_65, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.30  tff(c_80, plain, (![B_24, A_25]: (k3_tarski(k2_tarski(B_24, A_25))=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 2.11/1.30  tff(c_12, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.30  tff(c_86, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12])).
% 2.11/1.30  tff(c_18, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.30  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.30  tff(c_160, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_152])).
% 2.11/1.30  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k2_xboole_0(B_7, C_8)) | ~r1_tarski(k4_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.30  tff(c_192, plain, (![C_41]: (r1_tarski('#skF_1', k2_xboole_0('#skF_2', C_41)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), C_41))), inference(superposition, [status(thm), theory('equality')], [c_160, c_6])).
% 2.11/1.30  tff(c_198, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_192])).
% 2.11/1.30  tff(c_201, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_198])).
% 2.11/1.30  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_201])).
% 2.11/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  Inference rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Ref     : 0
% 2.11/1.30  #Sup     : 45
% 2.11/1.30  #Fact    : 0
% 2.11/1.30  #Define  : 0
% 2.11/1.30  #Split   : 0
% 2.11/1.30  #Chain   : 0
% 2.11/1.30  #Close   : 0
% 2.11/1.30  
% 2.11/1.30  Ordering : KBO
% 2.11/1.30  
% 2.11/1.30  Simplification rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Subsume      : 1
% 2.11/1.30  #Demod        : 4
% 2.11/1.30  #Tautology    : 34
% 2.11/1.30  #SimpNegUnit  : 1
% 2.11/1.30  #BackRed      : 0
% 2.11/1.30  
% 2.11/1.30  #Partial instantiations: 0
% 2.11/1.30  #Strategies tried      : 1
% 2.11/1.30  
% 2.11/1.30  Timing (in seconds)
% 2.11/1.30  ----------------------
% 2.11/1.30  Preprocessing        : 0.31
% 2.11/1.30  Parsing              : 0.16
% 2.11/1.30  CNF conversion       : 0.02
% 2.11/1.30  Main loop            : 0.17
% 2.11/1.30  Inferencing          : 0.06
% 2.11/1.30  Reduction            : 0.06
% 2.11/1.30  Demodulation         : 0.05
% 2.11/1.30  BG Simplification    : 0.01
% 2.11/1.30  Subsumption          : 0.02
% 2.11/1.30  Abstraction          : 0.01
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.50
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
