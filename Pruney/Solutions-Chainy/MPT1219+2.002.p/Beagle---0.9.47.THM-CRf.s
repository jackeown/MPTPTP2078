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
% DateTime   : Thu Dec  3 10:20:21 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  41 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > l1_struct_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( k3_subset_1(u1_struct_0(A),B) = k3_subset_1(u1_struct_0(A),C)
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( k3_subset_1(A,B) = k3_subset_1(A,C)
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21,plain,(
    ! [C_9,B_10,A_11] :
      ( C_9 = B_10
      | k3_subset_1(A_11,C_9) != k3_subset_1(A_11,B_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_23,plain,(
    ! [B_10] :
      ( B_10 = '#skF_2'
      | k3_subset_1(u1_struct_0('#skF_1'),B_10) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21])).

tff(c_30,plain,(
    ! [B_12] :
      ( B_12 = '#skF_2'
      | k3_subset_1(u1_struct_0('#skF_1'),B_12) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_23])).

tff(c_33,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_30])).

tff(c_40,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.07  
% 1.55/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.07  %$ m1_subset_1 > l1_struct_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.55/1.07  
% 1.55/1.07  %Foreground sorts:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Background operators:
% 1.55/1.07  
% 1.55/1.07  
% 1.55/1.07  %Foreground operators:
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.07  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.55/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.55/1.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.55/1.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.55/1.07  
% 1.55/1.08  tff(f_47, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((k3_subset_1(u1_struct_0(A), B) = k3_subset_1(u1_struct_0(A), C)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_1)).
% 1.55/1.08  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((k3_subset_1(A, B) = k3_subset_1(A, C)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_subset_1)).
% 1.55/1.08  tff(c_4, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.08  tff(c_8, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.08  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.08  tff(c_6, plain, (k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.08  tff(c_21, plain, (![C_9, B_10, A_11]: (C_9=B_10 | k3_subset_1(A_11, C_9)!=k3_subset_1(A_11, B_10) | ~m1_subset_1(C_9, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.55/1.08  tff(c_23, plain, (![B_10]: (B_10='#skF_2' | k3_subset_1(u1_struct_0('#skF_1'), B_10)!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21])).
% 1.55/1.08  tff(c_30, plain, (![B_12]: (B_12='#skF_2' | k3_subset_1(u1_struct_0('#skF_1'), B_12)!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_23])).
% 1.55/1.08  tff(c_33, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_8, c_30])).
% 1.55/1.08  tff(c_40, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_33])).
% 1.55/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.08  
% 1.55/1.08  Inference rules
% 1.55/1.08  ----------------------
% 1.55/1.08  #Ref     : 1
% 1.55/1.08  #Sup     : 6
% 1.55/1.08  #Fact    : 0
% 1.55/1.08  #Define  : 0
% 1.55/1.08  #Split   : 0
% 1.55/1.08  #Chain   : 0
% 1.55/1.08  #Close   : 0
% 1.55/1.08  
% 1.55/1.08  Ordering : KBO
% 1.55/1.08  
% 1.55/1.08  Simplification rules
% 1.55/1.08  ----------------------
% 1.55/1.08  #Subsume      : 0
% 1.55/1.08  #Demod        : 2
% 1.55/1.08  #Tautology    : 3
% 1.55/1.08  #SimpNegUnit  : 1
% 1.55/1.08  #BackRed      : 0
% 1.55/1.08  
% 1.55/1.08  #Partial instantiations: 0
% 1.55/1.08  #Strategies tried      : 1
% 1.55/1.08  
% 1.55/1.08  Timing (in seconds)
% 1.55/1.08  ----------------------
% 1.55/1.08  Preprocessing        : 0.26
% 1.55/1.09  Parsing              : 0.14
% 1.55/1.09  CNF conversion       : 0.02
% 1.55/1.09  Main loop            : 0.07
% 1.55/1.09  Inferencing          : 0.03
% 1.55/1.09  Reduction            : 0.02
% 1.55/1.09  Demodulation         : 0.02
% 1.55/1.09  BG Simplification    : 0.01
% 1.55/1.09  Subsumption          : 0.01
% 1.55/1.09  Abstraction          : 0.00
% 1.55/1.09  MUC search           : 0.00
% 1.55/1.09  Cooper               : 0.00
% 1.55/1.09  Total                : 0.35
% 1.55/1.09  Index Insertion      : 0.00
% 1.55/1.09  Index Deletion       : 0.00
% 1.55/1.09  Index Matching       : 0.00
% 1.55/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
