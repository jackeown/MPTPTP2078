%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:20 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  37 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( k3_subset_1(u1_struct_0(A),B) = k3_subset_1(u1_struct_0(A),C)
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_4,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    ! [A_7,B_8] :
      ( k3_subset_1(A_7,k3_subset_1(A_7,B_8)) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_17])).

tff(c_6,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_17])).

tff(c_24,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21])).

tff(c_29,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.09  %$ m1_subset_1 > l1_struct_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.58/1.09  
% 1.58/1.09  %Foreground sorts:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Background operators:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Foreground operators:
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.58/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.58/1.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.58/1.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.58/1.09  
% 1.58/1.10  tff(f_42, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((k3_subset_1(u1_struct_0(A), B) = k3_subset_1(u1_struct_0(A), C)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_1)).
% 1.58/1.10  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.58/1.10  tff(c_4, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.10  tff(c_8, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.10  tff(c_17, plain, (![A_7, B_8]: (k3_subset_1(A_7, k3_subset_1(A_7, B_8))=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.10  tff(c_22, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_8, c_17])).
% 1.58/1.10  tff(c_6, plain, (k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.10  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.58/1.10  tff(c_21, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_10, c_17])).
% 1.58/1.10  tff(c_24, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_21])).
% 1.58/1.10  tff(c_29, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 1.58/1.10  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_29])).
% 1.58/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  Inference rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Ref     : 0
% 1.58/1.10  #Sup     : 6
% 1.58/1.10  #Fact    : 0
% 1.58/1.10  #Define  : 0
% 1.58/1.10  #Split   : 0
% 1.58/1.10  #Chain   : 0
% 1.58/1.10  #Close   : 0
% 1.58/1.10  
% 1.58/1.10  Ordering : KBO
% 1.58/1.10  
% 1.58/1.10  Simplification rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Subsume      : 0
% 1.58/1.10  #Demod        : 2
% 1.58/1.10  #Tautology    : 4
% 1.58/1.10  #SimpNegUnit  : 1
% 1.58/1.10  #BackRed      : 0
% 1.58/1.10  
% 1.58/1.10  #Partial instantiations: 0
% 1.58/1.10  #Strategies tried      : 1
% 1.58/1.10  
% 1.58/1.10  Timing (in seconds)
% 1.58/1.10  ----------------------
% 1.58/1.11  Preprocessing        : 0.26
% 1.58/1.11  Parsing              : 0.14
% 1.58/1.11  CNF conversion       : 0.02
% 1.58/1.11  Main loop            : 0.07
% 1.58/1.11  Inferencing          : 0.03
% 1.58/1.11  Reduction            : 0.02
% 1.58/1.11  Demodulation         : 0.02
% 1.58/1.11  BG Simplification    : 0.01
% 1.58/1.11  Subsumption          : 0.01
% 1.58/1.11  Abstraction          : 0.00
% 1.58/1.11  MUC search           : 0.00
% 1.58/1.11  Cooper               : 0.00
% 1.58/1.11  Total                : 0.36
% 1.58/1.11  Index Insertion      : 0.00
% 1.58/1.11  Index Deletion       : 0.00
% 1.58/1.11  Index Matching       : 0.00
% 1.58/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
