%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_8,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_21,plain,(
    ! [A_12,B_13] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_12),B_13),A_12)
      | ~ v3_tops_1(B_13,A_12)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_tops_1(B_3,A_1)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_1),B_3),A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_14,A_15] :
      ( v2_tops_1(B_14,A_15)
      | ~ v3_tops_1(B_14,A_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_21,c_2])).

tff(c_29,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_26])).

tff(c_32,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_29])).

tff(c_34,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:05:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.08  
% 1.50/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.08  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > m1_subset_1 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.50/1.08  
% 1.50/1.08  %Foreground sorts:
% 1.50/1.08  
% 1.50/1.08  
% 1.50/1.08  %Background operators:
% 1.50/1.08  
% 1.50/1.08  
% 1.50/1.08  %Foreground operators:
% 1.50/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.08  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.50/1.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.50/1.08  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.50/1.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.50/1.08  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 1.50/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.50/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.50/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.50/1.08  
% 1.63/1.09  tff(f_53, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 1.63/1.09  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 1.63/1.09  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 1.63/1.09  tff(c_8, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.09  tff(c_14, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.09  tff(c_10, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.09  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.63/1.09  tff(c_21, plain, (![A_12, B_13]: (v1_tops_1(k3_subset_1(u1_struct_0(A_12), B_13), A_12) | ~v3_tops_1(B_13, A_12) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.09  tff(c_2, plain, (![B_3, A_1]: (v2_tops_1(B_3, A_1) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_1), B_3), A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.09  tff(c_26, plain, (![B_14, A_15]: (v2_tops_1(B_14, A_15) | ~v3_tops_1(B_14, A_15) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_21, c_2])).
% 1.63/1.09  tff(c_29, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_26])).
% 1.63/1.09  tff(c_32, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_29])).
% 1.63/1.09  tff(c_34, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_32])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 3
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
% 1.63/1.09  #Demod        : 2
% 1.63/1.09  #Tautology    : 1
% 1.63/1.09  #SimpNegUnit  : 1
% 1.63/1.09  #BackRed      : 0
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.25
% 1.63/1.09  Parsing              : 0.15
% 1.63/1.09  CNF conversion       : 0.02
% 1.63/1.09  Main loop            : 0.08
% 1.63/1.09  Inferencing          : 0.04
% 1.63/1.09  Reduction            : 0.02
% 1.63/1.09  Demodulation         : 0.02
% 1.63/1.09  BG Simplification    : 0.01
% 1.63/1.09  Subsumption          : 0.01
% 1.63/1.09  Abstraction          : 0.00
% 1.63/1.09  MUC search           : 0.00
% 1.63/1.09  Cooper               : 0.00
% 1.63/1.09  Total                : 0.36
% 1.63/1.09  Index Insertion      : 0.00
% 1.63/1.09  Index Deletion       : 0.00
% 1.63/1.09  Index Matching       : 0.00
% 1.63/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
