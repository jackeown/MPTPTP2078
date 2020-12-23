%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   33 (  52 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 101 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_10,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_92,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(k3_subset_1(A_16,C_17),k3_subset_1(A_16,B_18))
      | ~ r1_tarski(B_18,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_110,plain,(
    ! [C_17] :
      ( r1_tarski(k3_subset_1('#skF_1',C_17),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_134,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_137,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_143,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_111,plain,(
    ! [B_19,C_20,A_21] :
      ( r1_tarski(B_19,C_20)
      | ~ r1_tarski(k3_subset_1(A_21,C_20),k3_subset_1(A_21,B_19))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [C_20] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_20)
      | ~ r1_tarski(k3_subset_1('#skF_1',C_20),'#skF_3')
      | ~ m1_subset_1(C_20,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_157,plain,(
    ! [C_23] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_23)
      | ~ r1_tarski(k3_subset_1('#skF_1',C_23),'#skF_3')
      | ~ m1_subset_1(C_23,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_132])).

tff(c_166,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_157])).

tff(c_171,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  %$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.22  
% 2.01/1.23  tff(f_52, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 2.01/1.23  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.01/1.23  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.01/1.23  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.01/1.23  tff(c_10, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.23  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.23  tff(c_12, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.23  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.23  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.23  tff(c_17, plain, (![A_10, B_11]: (k3_subset_1(A_10, k3_subset_1(A_10, B_11))=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.23  tff(c_22, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_14, c_17])).
% 2.01/1.23  tff(c_92, plain, (![A_16, C_17, B_18]: (r1_tarski(k3_subset_1(A_16, C_17), k3_subset_1(A_16, B_18)) | ~r1_tarski(B_18, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.23  tff(c_110, plain, (![C_17]: (r1_tarski(k3_subset_1('#skF_1', C_17), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_17) | ~m1_subset_1(C_17, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_92])).
% 2.01/1.23  tff(c_134, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.01/1.23  tff(c_137, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2, c_134])).
% 2.01/1.23  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_137])).
% 2.01/1.23  tff(c_143, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_110])).
% 2.01/1.23  tff(c_111, plain, (![B_19, C_20, A_21]: (r1_tarski(B_19, C_20) | ~r1_tarski(k3_subset_1(A_21, C_20), k3_subset_1(A_21, B_19)) | ~m1_subset_1(C_20, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.23  tff(c_132, plain, (![C_20]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_20) | ~r1_tarski(k3_subset_1('#skF_1', C_20), '#skF_3') | ~m1_subset_1(C_20, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_111])).
% 2.01/1.23  tff(c_157, plain, (![C_23]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_23) | ~r1_tarski(k3_subset_1('#skF_1', C_23), '#skF_3') | ~m1_subset_1(C_23, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_132])).
% 2.01/1.23  tff(c_166, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_157])).
% 2.01/1.23  tff(c_171, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_166])).
% 2.01/1.23  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_171])).
% 2.01/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.23  
% 2.01/1.23  Inference rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Ref     : 0
% 2.01/1.23  #Sup     : 40
% 2.01/1.23  #Fact    : 0
% 2.01/1.23  #Define  : 0
% 2.01/1.23  #Split   : 1
% 2.01/1.23  #Chain   : 0
% 2.01/1.23  #Close   : 0
% 2.01/1.23  
% 2.01/1.23  Ordering : KBO
% 2.01/1.23  
% 2.01/1.23  Simplification rules
% 2.01/1.23  ----------------------
% 2.01/1.23  #Subsume      : 1
% 2.01/1.23  #Demod        : 14
% 2.01/1.23  #Tautology    : 18
% 2.01/1.23  #SimpNegUnit  : 1
% 2.01/1.23  #BackRed      : 0
% 2.01/1.23  
% 2.01/1.23  #Partial instantiations: 0
% 2.01/1.23  #Strategies tried      : 1
% 2.01/1.23  
% 2.01/1.23  Timing (in seconds)
% 2.01/1.23  ----------------------
% 2.01/1.23  Preprocessing        : 0.27
% 2.01/1.23  Parsing              : 0.16
% 2.01/1.23  CNF conversion       : 0.02
% 2.01/1.23  Main loop            : 0.17
% 2.01/1.23  Inferencing          : 0.07
% 2.01/1.23  Reduction            : 0.05
% 2.01/1.24  Demodulation         : 0.04
% 2.01/1.24  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.04
% 2.01/1.24  Abstraction          : 0.01
% 2.01/1.24  MUC search           : 0.00
% 2.01/1.24  Cooper               : 0.00
% 2.01/1.24  Total                : 0.46
% 2.01/1.24  Index Insertion      : 0.00
% 2.01/1.24  Index Deletion       : 0.00
% 2.01/1.24  Index Matching       : 0.00
% 2.01/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
