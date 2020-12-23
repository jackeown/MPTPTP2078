%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   35 (  52 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 ( 100 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_finset_1 > l1_struct_0 > k7_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(A),B))
            <=> v1_finset_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(A),B))
           => v1_finset_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_tops_2)).

tff(c_12,plain,
    ( ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19,plain,(
    ~ v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_8,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_18])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( k7_setfam_1(A_9,k7_setfam_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_21])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_13,A_14] :
      ( v1_finset_1(B_13)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(A_14),B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_19,B_20] :
      ( v1_finset_1(k7_setfam_1(u1_struct_0(A_19),B_20))
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(A_19),k7_setfam_1(u1_struct_0(A_19),B_20)))
      | ~ l1_struct_0(A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_116,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v1_finset_1('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_120,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_20,c_116])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_120])).

tff(c_123,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_124,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_143,plain,(
    ! [B_25,A_26] :
      ( v1_finset_1(B_25)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(A_26),B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_150,plain,
    ( v1_finset_1('#skF_2')
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_154,plain,(
    v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124,c_150])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:40:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.13  
% 1.81/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.14  %$ m1_subset_1 > v1_finset_1 > l1_struct_0 > k7_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.81/1.14  
% 1.81/1.14  %Foreground sorts:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Background operators:
% 1.81/1.14  
% 1.81/1.14  
% 1.81/1.14  %Foreground operators:
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.14  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.81/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.14  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.81/1.14  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.81/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.14  
% 1.81/1.15  tff(f_52, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(A), B)) <=> v1_finset_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tops_2)).
% 1.81/1.15  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 1.81/1.15  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 1.81/1.15  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(A), B)) => v1_finset_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_tops_2)).
% 1.81/1.15  tff(c_12, plain, (~v1_finset_1('#skF_2') | ~v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.15  tff(c_19, plain, (~v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_12])).
% 1.81/1.15  tff(c_8, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.15  tff(c_10, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.15  tff(c_18, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | v1_finset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.15  tff(c_20, plain, (v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_19, c_18])).
% 1.81/1.15  tff(c_21, plain, (![A_9, B_10]: (k7_setfam_1(A_9, k7_setfam_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.15  tff(c_24, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_8, c_21])).
% 1.81/1.15  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.15  tff(c_37, plain, (![B_13, A_14]: (v1_finset_1(B_13) | ~v1_finset_1(k7_setfam_1(u1_struct_0(A_14), B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.15  tff(c_102, plain, (![A_19, B_20]: (v1_finset_1(k7_setfam_1(u1_struct_0(A_19), B_20)) | ~v1_finset_1(k7_setfam_1(u1_struct_0(A_19), k7_setfam_1(u1_struct_0(A_19), B_20))) | ~l1_struct_0(A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))))), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.81/1.15  tff(c_116, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v1_finset_1('#skF_2') | ~l1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 1.81/1.15  tff(c_120, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_20, c_116])).
% 1.81/1.15  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_120])).
% 1.81/1.15  tff(c_123, plain, (~v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_12])).
% 1.81/1.15  tff(c_124, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_12])).
% 1.81/1.15  tff(c_143, plain, (![B_25, A_26]: (v1_finset_1(B_25) | ~v1_finset_1(k7_setfam_1(u1_struct_0(A_26), B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.15  tff(c_150, plain, (v1_finset_1('#skF_2') | ~v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_143])).
% 1.81/1.15  tff(c_154, plain, (v1_finset_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124, c_150])).
% 1.81/1.15  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_154])).
% 1.81/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.15  
% 1.81/1.15  Inference rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Ref     : 0
% 1.81/1.15  #Sup     : 31
% 1.81/1.15  #Fact    : 0
% 1.81/1.15  #Define  : 0
% 1.81/1.15  #Split   : 1
% 1.81/1.15  #Chain   : 0
% 1.81/1.15  #Close   : 0
% 1.81/1.15  
% 1.81/1.15  Ordering : KBO
% 1.81/1.15  
% 1.81/1.15  Simplification rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Subsume      : 2
% 1.81/1.15  #Demod        : 19
% 1.81/1.15  #Tautology    : 20
% 1.81/1.15  #SimpNegUnit  : 4
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.15  Preprocessing        : 0.26
% 1.81/1.15  Parsing              : 0.15
% 1.81/1.15  CNF conversion       : 0.02
% 1.81/1.15  Main loop            : 0.16
% 1.81/1.15  Inferencing          : 0.06
% 1.81/1.15  Reduction            : 0.04
% 1.81/1.15  Demodulation         : 0.03
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.03
% 1.81/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.44
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
