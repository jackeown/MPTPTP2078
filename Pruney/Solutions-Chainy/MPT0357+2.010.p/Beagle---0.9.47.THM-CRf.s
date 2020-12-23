%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  60 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k3_subset_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_10,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,B_6] : m1_subset_1(k6_subset_1(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_5,B_6] : m1_subset_1(k4_xboole_0(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6])).

tff(c_77,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_23])).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( k3_subset_1(A_22,k3_subset_1(A_22,B_23)) = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_106,plain,(
    ! [B_26,C_27,A_28] :
      ( r1_tarski(B_26,C_27)
      | ~ r1_tarski(k3_subset_1(A_28,C_27),k3_subset_1(A_28,B_26))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,(
    ! [C_27] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_27)
      | ~ r1_tarski(k3_subset_1('#skF_1',C_27),'#skF_3')
      | ~ m1_subset_1(C_27,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_106])).

tff(c_304,plain,(
    ! [C_40] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_40)
      | ~ r1_tarski(k3_subset_1('#skF_1',C_40),'#skF_3')
      | ~ m1_subset_1(C_40,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_118])).

tff(c_313,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_304])).

tff(c_322,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_313])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  %$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.23  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.23  
% 2.04/1.24  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 2.04/1.24  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.04/1.24  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.04/1.24  tff(f_33, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.04/1.24  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.04/1.24  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.04/1.24  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.24  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.24  tff(c_18, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.24  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.24  tff(c_61, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k3_subset_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.24  tff(c_72, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_61])).
% 2.04/1.24  tff(c_10, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.24  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k6_subset_1(A_5, B_6), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.24  tff(c_23, plain, (![A_5, B_6]: (m1_subset_1(k4_xboole_0(A_5, B_6), k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6])).
% 2.04/1.24  tff(c_77, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_23])).
% 2.04/1.24  tff(c_43, plain, (![A_22, B_23]: (k3_subset_1(A_22, k3_subset_1(A_22, B_23))=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.24  tff(c_51, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.04/1.24  tff(c_106, plain, (![B_26, C_27, A_28]: (r1_tarski(B_26, C_27) | ~r1_tarski(k3_subset_1(A_28, C_27), k3_subset_1(A_28, B_26)) | ~m1_subset_1(C_27, k1_zfmisc_1(A_28)) | ~m1_subset_1(B_26, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.24  tff(c_118, plain, (![C_27]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_27) | ~r1_tarski(k3_subset_1('#skF_1', C_27), '#skF_3') | ~m1_subset_1(C_27, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_51, c_106])).
% 2.04/1.24  tff(c_304, plain, (![C_40]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_40) | ~r1_tarski(k3_subset_1('#skF_1', C_40), '#skF_3') | ~m1_subset_1(C_40, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_118])).
% 2.04/1.24  tff(c_313, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_304])).
% 2.04/1.24  tff(c_322, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_313])).
% 2.04/1.24  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_322])).
% 2.04/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  Inference rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Ref     : 0
% 2.04/1.24  #Sup     : 74
% 2.04/1.24  #Fact    : 0
% 2.04/1.24  #Define  : 0
% 2.04/1.24  #Split   : 2
% 2.04/1.24  #Chain   : 0
% 2.04/1.24  #Close   : 0
% 2.04/1.24  
% 2.04/1.24  Ordering : KBO
% 2.04/1.24  
% 2.04/1.24  Simplification rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Subsume      : 1
% 2.04/1.24  #Demod        : 57
% 2.04/1.24  #Tautology    : 39
% 2.04/1.24  #SimpNegUnit  : 1
% 2.04/1.24  #BackRed      : 0
% 2.04/1.24  
% 2.04/1.24  #Partial instantiations: 0
% 2.04/1.24  #Strategies tried      : 1
% 2.04/1.24  
% 2.04/1.24  Timing (in seconds)
% 2.04/1.24  ----------------------
% 2.04/1.24  Preprocessing        : 0.26
% 2.04/1.24  Parsing              : 0.14
% 2.04/1.24  CNF conversion       : 0.02
% 2.04/1.24  Main loop            : 0.21
% 2.04/1.24  Inferencing          : 0.08
% 2.04/1.25  Reduction            : 0.07
% 2.04/1.25  Demodulation         : 0.06
% 2.04/1.25  BG Simplification    : 0.01
% 2.04/1.25  Subsumption          : 0.04
% 2.04/1.25  Abstraction          : 0.01
% 2.04/1.25  MUC search           : 0.00
% 2.04/1.25  Cooper               : 0.00
% 2.04/1.25  Total                : 0.49
% 2.04/1.25  Index Insertion      : 0.00
% 2.04/1.25  Index Deletion       : 0.00
% 2.04/1.25  Index Matching       : 0.00
% 2.04/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
