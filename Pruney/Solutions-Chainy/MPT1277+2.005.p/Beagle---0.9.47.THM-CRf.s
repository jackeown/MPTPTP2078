%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:08 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 102 expanded)
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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_tops_1(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_tops_1)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_5),B_7),A_5)
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ~ v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_23,plain,(
    ! [A_16,B_17] :
      ( k2_tops_1(A_16,k3_subset_1(u1_struct_0(A_16),B_17)) = k2_tops_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_32,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( v3_tops_1(k2_tops_1(A_20,B_21),A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ v3_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_24,B_25] :
      ( v3_tops_1(k2_tops_1(A_24,k3_subset_1(u1_struct_0(A_24),B_25)),A_24)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_24),B_25),A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24))) ) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_68,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_62])).

tff(c_70,plain,
    ( v3_tops_1(k2_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_18,c_68])).

tff(c_71,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_70])).

tff(c_74,plain,
    ( ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.14  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.67/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.67/1.14  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.67/1.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.67/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.67/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.14  
% 1.67/1.15  tff(f_67, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tops_1)).
% 1.67/1.15  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 1.67/1.15  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 1.67/1.15  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.67/1.15  tff(f_39, axiom, (![A, B]: ((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_tops_1(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_tops_1)).
% 1.67/1.15  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.15  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.15  tff(c_14, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.15  tff(c_8, plain, (![A_5, B_7]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_5), B_7), A_5) | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.15  tff(c_12, plain, (~v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.15  tff(c_20, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.67/1.15  tff(c_23, plain, (![A_16, B_17]: (k2_tops_1(A_16, k3_subset_1(u1_struct_0(A_16), B_17))=k2_tops_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.67/1.15  tff(c_28, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_23])).
% 1.67/1.15  tff(c_32, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_28])).
% 1.67/1.15  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.15  tff(c_42, plain, (![A_20, B_21]: (v3_tops_1(k2_tops_1(A_20, B_21), A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~v3_pre_topc(B_21, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.15  tff(c_62, plain, (![A_24, B_25]: (v3_tops_1(k2_tops_1(A_24, k3_subset_1(u1_struct_0(A_24), B_25)), A_24) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_24), B_25), A_24) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))))), inference(resolution, [status(thm)], [c_2, c_42])).
% 1.67/1.15  tff(c_68, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_62])).
% 1.67/1.15  tff(c_70, plain, (v3_tops_1(k2_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_18, c_68])).
% 1.67/1.15  tff(c_71, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_12, c_70])).
% 1.67/1.15  tff(c_74, plain, (~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_71])).
% 1.67/1.15  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_74])).
% 1.67/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.15  
% 1.67/1.15  Inference rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Ref     : 0
% 1.67/1.15  #Sup     : 12
% 1.67/1.15  #Fact    : 0
% 1.67/1.15  #Define  : 0
% 1.67/1.15  #Split   : 0
% 1.67/1.15  #Chain   : 0
% 1.67/1.15  #Close   : 0
% 1.67/1.15  
% 1.67/1.15  Ordering : KBO
% 1.67/1.15  
% 1.67/1.15  Simplification rules
% 1.67/1.15  ----------------------
% 1.67/1.15  #Subsume      : 0
% 1.67/1.15  #Demod        : 9
% 1.67/1.15  #Tautology    : 5
% 1.67/1.15  #SimpNegUnit  : 2
% 1.67/1.15  #BackRed      : 0
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.16  Preprocessing        : 0.26
% 1.67/1.16  Parsing              : 0.15
% 1.67/1.16  CNF conversion       : 0.02
% 1.67/1.16  Main loop            : 0.12
% 1.67/1.16  Inferencing          : 0.05
% 1.67/1.16  Reduction            : 0.03
% 1.67/1.16  Demodulation         : 0.02
% 1.67/1.16  BG Simplification    : 0.01
% 1.67/1.16  Subsumption          : 0.02
% 1.67/1.16  Abstraction          : 0.01
% 1.67/1.16  MUC search           : 0.00
% 1.67/1.16  Cooper               : 0.00
% 1.67/1.16  Total                : 0.41
% 1.67/1.16  Index Insertion      : 0.00
% 1.87/1.16  Index Deletion       : 0.00
% 1.87/1.16  Index Matching       : 0.00
% 1.87/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
