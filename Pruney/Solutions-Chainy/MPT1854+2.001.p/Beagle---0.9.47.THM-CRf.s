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
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   34 (  49 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 113 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_tex_2(k1_tex_2(A,B),A)
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tex_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_21,plain,(
    ! [A_7,B_8] :
      ( ~ v2_struct_0(k1_tex_2(A_7,B_8))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_27,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_28,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_27])).

tff(c_12,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,(
    ! [A_11,B_12] :
      ( m1_pre_topc(k1_tex_2(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_42,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_39])).

tff(c_43,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_42])).

tff(c_14,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [B_13,A_14] :
      ( ~ v1_tex_2(B_13,A_14)
      | v2_struct_0(B_13)
      | ~ m1_pre_topc(B_13,A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v7_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_50,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_43,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_28,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.30  
% 1.85/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.30  %$ v1_tex_2 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.85/1.30  
% 1.85/1.30  %Foreground sorts:
% 1.85/1.30  
% 1.85/1.30  
% 1.85/1.30  %Background operators:
% 1.85/1.30  
% 1.85/1.30  
% 1.85/1.30  %Foreground operators:
% 1.85/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.30  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.85/1.30  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.85/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.85/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.30  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.30  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 1.85/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.85/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.85/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.30  
% 2.02/1.31  tff(f_72, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_tex_2(k1_tex_2(A, B), A) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tex_2)).
% 2.02/1.31  tff(f_58, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.02/1.31  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.02/1.31  tff(c_20, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.31  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.31  tff(c_16, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.31  tff(c_21, plain, (![A_7, B_8]: (~v2_struct_0(k1_tex_2(A_7, B_8)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.31  tff(c_24, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_21])).
% 2.02/1.31  tff(c_27, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 2.02/1.31  tff(c_28, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_20, c_27])).
% 2.02/1.31  tff(c_12, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.31  tff(c_37, plain, (![A_11, B_12]: (m1_pre_topc(k1_tex_2(A_11, B_12), A_11) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.31  tff(c_39, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.02/1.31  tff(c_42, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_39])).
% 2.02/1.31  tff(c_43, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_20, c_42])).
% 2.02/1.31  tff(c_14, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.31  tff(c_44, plain, (![B_13, A_14]: (~v1_tex_2(B_13, A_14) | v2_struct_0(B_13) | ~m1_pre_topc(B_13, A_14) | ~l1_pre_topc(A_14) | ~v7_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.31  tff(c_47, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.02/1.31  tff(c_50, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_43, c_47])).
% 2.02/1.31  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_28, c_50])).
% 2.02/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  Inference rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Ref     : 0
% 2.02/1.31  #Sup     : 4
% 2.02/1.31  #Fact    : 0
% 2.02/1.31  #Define  : 0
% 2.02/1.31  #Split   : 0
% 2.02/1.31  #Chain   : 0
% 2.02/1.31  #Close   : 0
% 2.02/1.31  
% 2.02/1.31  Ordering : KBO
% 2.02/1.31  
% 2.02/1.31  Simplification rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Subsume      : 0
% 2.02/1.31  #Demod        : 6
% 2.02/1.31  #Tautology    : 1
% 2.02/1.31  #SimpNegUnit  : 4
% 2.02/1.31  #BackRed      : 0
% 2.02/1.31  
% 2.02/1.31  #Partial instantiations: 0
% 2.02/1.31  #Strategies tried      : 1
% 2.02/1.31  
% 2.02/1.31  Timing (in seconds)
% 2.02/1.31  ----------------------
% 2.02/1.31  Preprocessing        : 0.36
% 2.02/1.31  Parsing              : 0.19
% 2.02/1.31  CNF conversion       : 0.03
% 2.02/1.31  Main loop            : 0.11
% 2.02/1.31  Inferencing          : 0.05
% 2.02/1.31  Reduction            : 0.03
% 2.02/1.31  Demodulation         : 0.02
% 2.02/1.31  BG Simplification    : 0.02
% 2.02/1.31  Subsumption          : 0.02
% 2.02/1.32  Abstraction          : 0.00
% 2.02/1.32  MUC search           : 0.00
% 2.02/1.32  Cooper               : 0.00
% 2.02/1.32  Total                : 0.50
% 2.02/1.32  Index Insertion      : 0.00
% 2.02/1.32  Index Deletion       : 0.00
% 2.02/1.32  Index Matching       : 0.00
% 2.02/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
