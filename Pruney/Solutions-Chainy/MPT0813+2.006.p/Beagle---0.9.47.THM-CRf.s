%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  35 expanded)
%              Number of equality atoms :    3 (   3 expanded)
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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ( r1_tarski(A,D)
         => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_37,plain,(
    k2_xboole_0('#skF_1','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_46,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(k2_xboole_0(A_14,B_16),C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [C_17] :
      ( r1_tarski('#skF_1',C_17)
      | ~ r1_tarski('#skF_4',C_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_46])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_10])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_53,c_28])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.08  
% 1.63/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.08  %$ r1_tarski > m1_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.08  
% 1.63/1.08  %Foreground sorts:
% 1.63/1.08  
% 1.63/1.08  
% 1.63/1.08  %Background operators:
% 1.63/1.08  
% 1.63/1.08  
% 1.63/1.08  %Foreground operators:
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.08  
% 1.63/1.09  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 1.63/1.09  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.63/1.09  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.63/1.09  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.63/1.09  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.09  tff(c_15, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.09  tff(c_19, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_15])).
% 1.63/1.09  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.09  tff(c_29, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.09  tff(c_37, plain, (k2_xboole_0('#skF_1', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.63/1.09  tff(c_46, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(k2_xboole_0(A_14, B_16), C_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_53, plain, (![C_17]: (r1_tarski('#skF_1', C_17) | ~r1_tarski('#skF_4', C_17))), inference(superposition, [status(thm), theory('equality')], [c_37, c_46])).
% 1.63/1.09  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.09  tff(c_10, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.09  tff(c_28, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_10])).
% 1.63/1.09  tff(c_59, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_28])).
% 1.63/1.09  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19, c_59])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 13
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 0
% 1.63/1.09  #Chain   : 0
% 1.63/1.09  #Close   : 0
% 1.63/1.09  
% 1.63/1.09  Ordering : KBO
% 1.63/1.09  
% 1.63/1.09  Simplification rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Subsume      : 0
% 1.63/1.09  #Demod        : 1
% 1.63/1.09  #Tautology    : 5
% 1.63/1.09  #SimpNegUnit  : 0
% 1.63/1.09  #BackRed      : 0
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.25
% 1.63/1.09  Parsing              : 0.14
% 1.63/1.09  CNF conversion       : 0.01
% 1.63/1.09  Main loop            : 0.09
% 1.63/1.09  Inferencing          : 0.04
% 1.63/1.09  Reduction            : 0.02
% 1.63/1.09  Demodulation         : 0.02
% 1.63/1.09  BG Simplification    : 0.01
% 1.63/1.09  Subsumption          : 0.01
% 1.63/1.09  Abstraction          : 0.00
% 1.63/1.09  MUC search           : 0.00
% 1.63/1.09  Cooper               : 0.00
% 1.63/1.10  Total                : 0.36
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
