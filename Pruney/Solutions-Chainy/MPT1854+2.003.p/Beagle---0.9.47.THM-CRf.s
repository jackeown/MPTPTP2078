%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   33 (  39 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  76 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_tex_2(k1_tex_2(A,B),A)
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v1_tex_2(k1_tex_2(A,B),A)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21,plain,(
    ! [A_12,B_13] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_12),B_13),u1_struct_0(A_12))
      | ~ v1_tex_2(k1_tex_2(A_12,B_13),A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( ~ v7_struct_0(A_5)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_5),B_7),u1_struct_0(A_5))
      | ~ m1_subset_1(B_7,u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( ~ v7_struct_0(A_14)
      | ~ l1_struct_0(A_14)
      | ~ v1_tex_2(k1_tex_2(A_14,B_15),A_14)
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_21,c_8])).

tff(c_29,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_26])).

tff(c_32,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_10,c_29])).

tff(c_33,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_32])).

tff(c_36,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_40,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.08  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.68/1.08  
% 1.68/1.08  %Foreground sorts:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Background operators:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Foreground operators:
% 1.68/1.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.08  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.68/1.08  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 1.68/1.08  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.68/1.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.68/1.08  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.68/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.08  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.68/1.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.08  
% 1.68/1.09  tff(f_68, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_tex_2(k1_tex_2(A, B), A) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tex_2)).
% 1.68/1.09  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.68/1.09  tff(f_41, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 1.68/1.09  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 1.68/1.09  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.68/1.09  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.09  tff(c_18, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.68/1.09  tff(c_14, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.68/1.09  tff(c_10, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.68/1.09  tff(c_12, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.68/1.09  tff(c_21, plain, (![A_12, B_13]: (v1_subset_1(k6_domain_1(u1_struct_0(A_12), B_13), u1_struct_0(A_12)) | ~v1_tex_2(k1_tex_2(A_12, B_13), A_12) | ~m1_subset_1(B_13, u1_struct_0(A_12)) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.09  tff(c_8, plain, (![A_5, B_7]: (~v7_struct_0(A_5) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_5), B_7), u1_struct_0(A_5)) | ~m1_subset_1(B_7, u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.68/1.09  tff(c_26, plain, (![A_14, B_15]: (~v7_struct_0(A_14) | ~l1_struct_0(A_14) | ~v1_tex_2(k1_tex_2(A_14, B_15), A_14) | ~m1_subset_1(B_15, u1_struct_0(A_14)) | ~l1_pre_topc(A_14) | v2_struct_0(A_14))), inference(resolution, [status(thm)], [c_21, c_8])).
% 1.68/1.09  tff(c_29, plain, (~v7_struct_0('#skF_1') | ~l1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_26])).
% 1.68/1.09  tff(c_32, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_10, c_29])).
% 1.68/1.09  tff(c_33, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_32])).
% 1.68/1.09  tff(c_36, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_33])).
% 1.68/1.09  tff(c_40, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 1.68/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  Inference rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Ref     : 0
% 1.68/1.09  #Sup     : 3
% 1.68/1.09  #Fact    : 0
% 1.68/1.09  #Define  : 0
% 1.68/1.09  #Split   : 0
% 1.68/1.09  #Chain   : 0
% 1.68/1.09  #Close   : 0
% 1.68/1.09  
% 1.68/1.09  Ordering : KBO
% 1.68/1.09  
% 1.68/1.09  Simplification rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Subsume      : 0
% 1.68/1.09  #Demod        : 4
% 1.68/1.09  #Tautology    : 0
% 1.68/1.09  #SimpNegUnit  : 1
% 1.68/1.09  #BackRed      : 0
% 1.68/1.09  
% 1.68/1.09  #Partial instantiations: 0
% 1.68/1.09  #Strategies tried      : 1
% 1.68/1.09  
% 1.68/1.09  Timing (in seconds)
% 1.68/1.09  ----------------------
% 1.68/1.09  Preprocessing        : 0.26
% 1.68/1.09  Parsing              : 0.15
% 1.68/1.09  CNF conversion       : 0.02
% 1.68/1.09  Main loop            : 0.09
% 1.68/1.09  Inferencing          : 0.04
% 1.68/1.09  Reduction            : 0.02
% 1.68/1.09  Demodulation         : 0.02
% 1.68/1.10  BG Simplification    : 0.01
% 1.68/1.10  Subsumption          : 0.01
% 1.68/1.10  Abstraction          : 0.00
% 1.68/1.10  MUC search           : 0.00
% 1.68/1.10  Cooper               : 0.00
% 1.68/1.10  Total                : 0.37
% 1.68/1.10  Index Insertion      : 0.00
% 1.68/1.10  Index Deletion       : 0.00
% 1.68/1.10  Index Matching       : 0.00
% 1.68/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
