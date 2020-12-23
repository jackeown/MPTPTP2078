%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:55 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  85 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [B_39,A_40] :
      ( v1_subset_1(u1_struct_0(B_39),u1_struct_0(A_40))
      | ~ m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v1_tex_2(B_39,A_40)
      | ~ m1_pre_topc(B_39,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [B_41,A_42] :
      ( v1_subset_1(u1_struct_0(B_41),u1_struct_0(A_42))
      | ~ v1_tex_2(B_41,A_42)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_213,plain,(
    ! [B_41] :
      ( v1_subset_1(u1_struct_0(B_41),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_41,'#skF_2')
      | ~ m1_pre_topc(B_41,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_249,plain,(
    ! [B_46] :
      ( v1_subset_1(u1_struct_0(B_46),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_46,'#skF_2')
      | ~ m1_pre_topc(B_46,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_213])).

tff(c_29,plain,(
    ! [B_20,A_21] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_pre_topc(B_20,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [B_20] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_20,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_29])).

tff(c_47,plain,(
    ! [B_22] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_22,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_14,plain,(
    ! [B_15] :
      ( ~ v1_subset_1(B_15,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_14])).

tff(c_61,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_256,plain,
    ( ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_61])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  
% 2.03/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.29  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.29  
% 2.03/1.29  %Foreground sorts:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Background operators:
% 2.03/1.29  
% 2.03/1.29  
% 2.03/1.29  %Foreground operators:
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.03/1.29  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.03/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.03/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.03/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.03/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.29  
% 2.10/1.30  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tex_2)).
% 2.10/1.30  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.10/1.30  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.10/1.30  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.10/1.30  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_16, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_18, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.30  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.30  tff(c_178, plain, (![B_39, A_40]: (v1_subset_1(u1_struct_0(B_39), u1_struct_0(A_40)) | ~m1_subset_1(u1_struct_0(B_39), k1_zfmisc_1(u1_struct_0(A_40))) | ~v1_tex_2(B_39, A_40) | ~m1_pre_topc(B_39, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.30  tff(c_200, plain, (![B_41, A_42]: (v1_subset_1(u1_struct_0(B_41), u1_struct_0(A_42)) | ~v1_tex_2(B_41, A_42) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_2, c_178])).
% 2.10/1.30  tff(c_213, plain, (![B_41]: (v1_subset_1(u1_struct_0(B_41), u1_struct_0('#skF_3')) | ~v1_tex_2(B_41, '#skF_2') | ~m1_pre_topc(B_41, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_200])).
% 2.10/1.30  tff(c_249, plain, (![B_46]: (v1_subset_1(u1_struct_0(B_46), u1_struct_0('#skF_3')) | ~v1_tex_2(B_46, '#skF_2') | ~m1_pre_topc(B_46, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_213])).
% 2.10/1.30  tff(c_29, plain, (![B_20, A_21]: (m1_subset_1(u1_struct_0(B_20), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_pre_topc(B_20, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.30  tff(c_42, plain, (![B_20]: (m1_subset_1(u1_struct_0(B_20), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_20, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_29])).
% 2.10/1.30  tff(c_47, plain, (![B_22]: (m1_subset_1(u1_struct_0(B_22), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_22, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 2.10/1.30  tff(c_14, plain, (![B_15]: (~v1_subset_1(B_15, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.30  tff(c_54, plain, (~v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_47, c_14])).
% 2.10/1.30  tff(c_61, plain, (~v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54])).
% 2.10/1.30  tff(c_256, plain, (~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_249, c_61])).
% 2.10/1.30  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_256])).
% 2.10/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  Inference rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Ref     : 0
% 2.10/1.30  #Sup     : 46
% 2.10/1.30  #Fact    : 0
% 2.10/1.30  #Define  : 0
% 2.10/1.30  #Split   : 2
% 2.10/1.30  #Chain   : 0
% 2.10/1.30  #Close   : 0
% 2.10/1.30  
% 2.10/1.30  Ordering : KBO
% 2.10/1.30  
% 2.10/1.30  Simplification rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Subsume      : 14
% 2.10/1.30  #Demod        : 27
% 2.10/1.30  #Tautology    : 8
% 2.10/1.30  #SimpNegUnit  : 3
% 2.10/1.30  #BackRed      : 0
% 2.10/1.30  
% 2.10/1.30  #Partial instantiations: 0
% 2.10/1.30  #Strategies tried      : 1
% 2.10/1.30  
% 2.10/1.30  Timing (in seconds)
% 2.10/1.30  ----------------------
% 2.10/1.30  Preprocessing        : 0.26
% 2.10/1.30  Parsing              : 0.14
% 2.10/1.30  CNF conversion       : 0.02
% 2.10/1.30  Main loop            : 0.19
% 2.10/1.30  Inferencing          : 0.07
% 2.10/1.30  Reduction            : 0.05
% 2.10/1.30  Demodulation         : 0.04
% 2.10/1.30  BG Simplification    : 0.01
% 2.10/1.30  Subsumption          : 0.05
% 2.10/1.30  Abstraction          : 0.01
% 2.10/1.30  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.48
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
