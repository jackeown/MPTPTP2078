%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  82 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [B_21,A_22] :
      ( v1_subset_1(u1_struct_0(B_21),u1_struct_0(A_22))
      | ~ v1_tex_2(B_21,A_22)
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [B_23,A_24] :
      ( v1_subset_1(u1_struct_0(B_23),u1_struct_0(A_24))
      | ~ v1_tex_2(B_23,A_24)
      | ~ m1_pre_topc(B_23,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_103,plain,(
    ! [A_25] :
      ( v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0(A_25))
      | ~ v1_tex_2('#skF_2',A_25)
      | ~ m1_pre_topc('#skF_2',A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_25,plain,(
    ! [B_17,A_18] :
      ( m1_subset_1(u1_struct_0(B_17),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_pre_topc(B_17,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_20] :
      ( m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc('#skF_2',A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_6,plain,(
    ! [B_5] :
      ( ~ v1_subset_1(B_5,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_6])).

tff(c_66,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_59])).

tff(c_106,plain,
    ( ~ v1_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_66])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:19:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.23  
% 1.80/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.23  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.80/1.23  
% 1.80/1.23  %Foreground sorts:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Background operators:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Foreground operators:
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.80/1.23  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.80/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.80/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.80/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.80/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.23  
% 1.80/1.24  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 1.80/1.24  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.80/1.24  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 1.80/1.24  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 1.80/1.24  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.24  tff(c_16, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.24  tff(c_12, plain, (v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.24  tff(c_14, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.24  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.24  tff(c_67, plain, (![B_21, A_22]: (v1_subset_1(u1_struct_0(B_21), u1_struct_0(A_22)) | ~v1_tex_2(B_21, A_22) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_21, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.24  tff(c_84, plain, (![B_23, A_24]: (v1_subset_1(u1_struct_0(B_23), u1_struct_0(A_24)) | ~v1_tex_2(B_23, A_24) | ~m1_pre_topc(B_23, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_2, c_67])).
% 1.80/1.24  tff(c_103, plain, (![A_25]: (v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0(A_25)) | ~v1_tex_2('#skF_2', A_25) | ~m1_pre_topc('#skF_2', A_25) | ~l1_pre_topc(A_25))), inference(superposition, [status(thm), theory('equality')], [c_14, c_84])).
% 1.80/1.24  tff(c_25, plain, (![B_17, A_18]: (m1_subset_1(u1_struct_0(B_17), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_pre_topc(B_17, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.80/1.24  tff(c_52, plain, (![A_20]: (m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc('#skF_2', A_20) | ~l1_pre_topc(A_20))), inference(superposition, [status(thm), theory('equality')], [c_14, c_25])).
% 1.80/1.24  tff(c_6, plain, (![B_5]: (~v1_subset_1(B_5, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.24  tff(c_59, plain, (~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_6])).
% 1.80/1.24  tff(c_66, plain, (~v1_subset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_59])).
% 1.80/1.24  tff(c_106, plain, (~v1_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_103, c_66])).
% 1.80/1.24  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_106])).
% 1.80/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.24  
% 1.80/1.24  Inference rules
% 1.80/1.24  ----------------------
% 1.80/1.24  #Ref     : 0
% 1.80/1.24  #Sup     : 22
% 1.80/1.24  #Fact    : 0
% 1.80/1.24  #Define  : 0
% 1.80/1.24  #Split   : 3
% 1.80/1.24  #Chain   : 0
% 1.80/1.24  #Close   : 0
% 1.80/1.24  
% 1.80/1.24  Ordering : KBO
% 1.80/1.24  
% 1.80/1.24  Simplification rules
% 1.80/1.24  ----------------------
% 1.80/1.24  #Subsume      : 6
% 1.80/1.24  #Demod        : 10
% 1.80/1.24  #Tautology    : 2
% 1.80/1.24  #SimpNegUnit  : 0
% 1.80/1.24  #BackRed      : 0
% 1.80/1.24  
% 1.80/1.24  #Partial instantiations: 0
% 1.80/1.24  #Strategies tried      : 1
% 1.80/1.24  
% 1.80/1.24  Timing (in seconds)
% 1.80/1.24  ----------------------
% 1.80/1.24  Preprocessing        : 0.30
% 1.80/1.24  Parsing              : 0.16
% 1.80/1.24  CNF conversion       : 0.02
% 1.80/1.24  Main loop            : 0.13
% 1.80/1.24  Inferencing          : 0.04
% 1.80/1.24  Reduction            : 0.04
% 1.80/1.24  Demodulation         : 0.03
% 1.80/1.24  BG Simplification    : 0.01
% 1.80/1.24  Subsumption          : 0.03
% 1.80/1.24  Abstraction          : 0.01
% 1.80/1.24  MUC search           : 0.00
% 1.80/1.24  Cooper               : 0.00
% 1.80/1.24  Total                : 0.45
% 1.80/1.24  Index Insertion      : 0.00
% 1.80/1.25  Index Deletion       : 0.00
% 1.80/1.25  Index Matching       : 0.00
% 1.80/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
