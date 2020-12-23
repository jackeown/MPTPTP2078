%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:08 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 111 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tops_1)).

tff(c_18,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_3),B_4),A_3)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ v4_pre_topc(B_4,A_3)
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ~ v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k2_tops_1(A_14,k3_subset_1(u1_struct_0(A_14),B_15)) = k2_tops_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_20])).

tff(c_29,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( v3_tops_1(k2_tops_1(A_16,B_17),A_16)
      | ~ v3_pre_topc(B_17,A_16)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_22,B_23] :
      ( v3_tops_1(k2_tops_1(A_22,k3_subset_1(u1_struct_0(A_22),B_23)),A_22)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_22),B_23),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22))) ) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_61,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_55])).

tff(c_63,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_16,c_61])).

tff(c_64,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_63])).

tff(c_67,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_14,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.48  
% 2.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.49  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.14/1.49  
% 2.14/1.49  %Foreground sorts:
% 2.14/1.49  
% 2.14/1.49  
% 2.14/1.49  %Background operators:
% 2.14/1.49  
% 2.14/1.49  
% 2.14/1.49  %Foreground operators:
% 2.14/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.49  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.14/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.49  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.14/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.14/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.49  
% 2.14/1.50  tff(f_69, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tops_1)).
% 2.14/1.50  tff(f_39, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tops_1)).
% 2.14/1.50  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 2.14/1.50  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.14/1.50  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tops_1)).
% 2.14/1.50  tff(c_18, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.50  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.50  tff(c_12, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.50  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.50  tff(c_4, plain, (![A_3, B_4]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_3), B_4), A_3) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~v4_pre_topc(B_4, A_3) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.50  tff(c_10, plain, (~v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.50  tff(c_20, plain, (![A_14, B_15]: (k2_tops_1(A_14, k3_subset_1(u1_struct_0(A_14), B_15))=k2_tops_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.50  tff(c_25, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_20])).
% 2.14/1.50  tff(c_29, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25])).
% 2.14/1.50  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.50  tff(c_34, plain, (![A_16, B_17]: (v3_tops_1(k2_tops_1(A_16, B_17), A_16) | ~v3_pre_topc(B_17, A_16) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.50  tff(c_55, plain, (![A_22, B_23]: (v3_tops_1(k2_tops_1(A_22, k3_subset_1(u1_struct_0(A_22), B_23)), A_22) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_22), B_23), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))))), inference(resolution, [status(thm)], [c_2, c_34])).
% 2.14/1.50  tff(c_61, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_29, c_55])).
% 2.14/1.50  tff(c_63, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_16, c_61])).
% 2.14/1.50  tff(c_64, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_10, c_63])).
% 2.14/1.50  tff(c_67, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_64])).
% 2.14/1.50  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_14, c_67])).
% 2.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.50  
% 2.14/1.50  Inference rules
% 2.14/1.50  ----------------------
% 2.14/1.50  #Ref     : 0
% 2.14/1.50  #Sup     : 11
% 2.14/1.50  #Fact    : 0
% 2.14/1.50  #Define  : 0
% 2.14/1.50  #Split   : 0
% 2.14/1.50  #Chain   : 0
% 2.14/1.50  #Close   : 0
% 2.14/1.50  
% 2.14/1.50  Ordering : KBO
% 2.14/1.50  
% 2.14/1.50  Simplification rules
% 2.14/1.50  ----------------------
% 2.14/1.50  #Subsume      : 0
% 2.14/1.50  #Demod        : 10
% 2.14/1.50  #Tautology    : 4
% 2.14/1.50  #SimpNegUnit  : 2
% 2.14/1.50  #BackRed      : 0
% 2.14/1.50  
% 2.14/1.50  #Partial instantiations: 0
% 2.14/1.50  #Strategies tried      : 1
% 2.14/1.50  
% 2.14/1.50  Timing (in seconds)
% 2.14/1.50  ----------------------
% 2.14/1.50  Preprocessing        : 0.42
% 2.14/1.50  Parsing              : 0.23
% 2.14/1.50  CNF conversion       : 0.03
% 2.14/1.50  Main loop            : 0.17
% 2.14/1.50  Inferencing          : 0.08
% 2.14/1.50  Reduction            : 0.04
% 2.14/1.50  Demodulation         : 0.03
% 2.14/1.50  BG Simplification    : 0.01
% 2.14/1.50  Subsumption          : 0.03
% 2.14/1.50  Abstraction          : 0.01
% 2.14/1.50  MUC search           : 0.00
% 2.14/1.50  Cooper               : 0.00
% 2.14/1.50  Total                : 0.63
% 2.14/1.50  Index Insertion      : 0.00
% 2.14/1.50  Index Deletion       : 0.00
% 2.14/1.50  Index Matching       : 0.00
% 2.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
