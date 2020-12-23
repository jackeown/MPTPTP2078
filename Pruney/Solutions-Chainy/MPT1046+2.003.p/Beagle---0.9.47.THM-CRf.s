%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  97 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k3_partfun1(B,A,A))
        & v1_partfun1(k3_partfun1(B,A,A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_2)).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    ! [C_9,A_10,B_11] :
      ( k3_partfun1(C_9,A_10,B_11) = C_9
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_19])).

tff(c_25,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_12,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_12])).

tff(c_39,plain,(
    ! [A_14,B_15,C_16] :
      ( k5_partfun1(A_14,B_15,C_16) = k1_tarski(C_16)
      | ~ v1_partfun1(C_16,A_14)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_45,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_46,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_45])).

tff(c_16,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [B_20,A_21] :
      ( v1_partfun1(k3_partfun1(B_20,A_21,A_21),A_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v1_funct_2(B_20,A_21,A_21)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,
    ( v1_partfun1(k3_partfun1('#skF_2','#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_55])).

tff(c_60,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_25,c_57])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 1.71/1.11  
% 1.71/1.11  %Foreground sorts:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Background operators:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Foreground operators:
% 1.71/1.11  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.71/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.71/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.71/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.11  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.71/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.11  
% 1.71/1.11  tff(f_58, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_2)).
% 1.71/1.11  tff(f_49, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.71/1.11  tff(f_43, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 1.71/1.11  tff(f_35, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v1_funct_1(k3_partfun1(B, A, A)) & v1_partfun1(k3_partfun1(B, A, A), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_2)).
% 1.71/1.11  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_19, plain, (![C_9, A_10, B_11]: (k3_partfun1(C_9, A_10, B_11)=C_9 | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.11  tff(c_22, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_19])).
% 1.71/1.11  tff(c_25, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.71/1.11  tff(c_12, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_33, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_12])).
% 1.71/1.11  tff(c_39, plain, (![A_14, B_15, C_16]: (k5_partfun1(A_14, B_15, C_16)=k1_tarski(C_16) | ~v1_partfun1(C_16, A_14) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.71/1.11  tff(c_42, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_39])).
% 1.71/1.11  tff(c_45, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42])).
% 1.71/1.11  tff(c_46, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_33, c_45])).
% 1.71/1.11  tff(c_16, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.11  tff(c_55, plain, (![B_20, A_21]: (v1_partfun1(k3_partfun1(B_20, A_21, A_21), A_21) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v1_funct_2(B_20, A_21, A_21) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.11  tff(c_57, plain, (v1_partfun1(k3_partfun1('#skF_2', '#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_55])).
% 1.71/1.11  tff(c_60, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_25, c_57])).
% 1.71/1.11  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_60])).
% 1.71/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  Inference rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Ref     : 0
% 1.71/1.11  #Sup     : 7
% 1.71/1.11  #Fact    : 0
% 1.71/1.11  #Define  : 0
% 1.71/1.11  #Split   : 0
% 1.71/1.11  #Chain   : 0
% 1.71/1.11  #Close   : 0
% 1.71/1.11  
% 1.71/1.11  Ordering : KBO
% 1.71/1.11  
% 1.71/1.11  Simplification rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Subsume      : 1
% 1.71/1.11  #Demod        : 11
% 1.71/1.11  #Tautology    : 3
% 1.71/1.12  #SimpNegUnit  : 3
% 1.71/1.12  #BackRed      : 1
% 1.71/1.12  
% 1.71/1.12  #Partial instantiations: 0
% 1.71/1.12  #Strategies tried      : 1
% 1.71/1.12  
% 1.71/1.12  Timing (in seconds)
% 1.71/1.12  ----------------------
% 1.71/1.12  Preprocessing        : 0.27
% 1.71/1.12  Parsing              : 0.15
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.08
% 1.71/1.12  Inferencing          : 0.03
% 1.71/1.12  Reduction            : 0.03
% 1.71/1.12  Demodulation         : 0.02
% 1.71/1.12  BG Simplification    : 0.01
% 1.71/1.12  Subsumption          : 0.01
% 1.71/1.12  Abstraction          : 0.01
% 1.71/1.12  MUC search           : 0.00
% 1.71/1.12  Cooper               : 0.00
% 1.71/1.12  Total                : 0.38
% 1.71/1.12  Index Insertion      : 0.00
% 1.71/1.12  Index Deletion       : 0.00
% 1.71/1.12  Index Matching       : 0.00
% 1.71/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
