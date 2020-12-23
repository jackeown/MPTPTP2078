%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  50 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_9] :
      ( l1_orders_2(k7_lattice3(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_10] :
      ( g1_orders_2(u1_struct_0(A_10),u1_orders_2(A_10)) = k7_lattice3(k7_lattice3(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [A_23] :
      ( g1_orders_2(u1_struct_0(A_23),k3_relset_1(u1_struct_0(A_23),u1_struct_0(A_23),u1_orders_2(A_23))) = k7_lattice3(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_orders_2(C_6,D_7) != g1_orders_2(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k2_zfmisc_1(A_2,A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [A_24,A_25,B_26] :
      ( u1_struct_0(A_24) = A_25
      | k7_lattice3(A_24) != g1_orders_2(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ l1_orders_2(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_6])).

tff(c_70,plain,(
    ! [A_24,A_10] :
      ( u1_struct_0(A_24) = u1_struct_0(A_10)
      | k7_lattice3(k7_lattice3(A_10)) != k7_lattice3(A_24)
      | ~ m1_subset_1(u1_orders_2(A_10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_10),u1_struct_0(A_10))))
      | ~ l1_orders_2(A_24)
      | ~ l1_orders_2(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_66])).

tff(c_105,plain,(
    ! [A_47] :
      ( u1_struct_0(k7_lattice3(A_47)) = u1_struct_0(A_47)
      | ~ m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ l1_orders_2(k7_lattice3(A_47))
      | ~ l1_orders_2(A_47) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_70])).

tff(c_110,plain,(
    ! [A_48] :
      ( u1_struct_0(k7_lattice3(A_48)) = u1_struct_0(A_48)
      | ~ l1_orders_2(k7_lattice3(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_115,plain,(
    ! [A_49] :
      ( u1_struct_0(k7_lattice3(A_49)) = u1_struct_0(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_16,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_16])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 1.89/1.21  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.89/1.21  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.89/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.21  
% 1.89/1.22  tff(f_57, negated_conjecture, ~(![A]: (l1_orders_2(A) => (u1_struct_0(A) = u1_struct_0(k7_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_6)).
% 1.89/1.22  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(k7_lattice3(A)) & l1_orders_2(k7_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattice3)).
% 1.89/1.22  tff(f_29, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.89/1.22  tff(f_52, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_lattice3)).
% 1.89/1.22  tff(f_42, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattice3)).
% 1.89/1.22  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 1.89/1.22  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.22  tff(c_10, plain, (![A_9]: (l1_orders_2(k7_lattice3(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_orders_2(A_1), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(A_1)))) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.22  tff(c_14, plain, (![A_10]: (g1_orders_2(u1_struct_0(A_10), u1_orders_2(A_10))=k7_lattice3(k7_lattice3(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.22  tff(c_49, plain, (![A_23]: (g1_orders_2(u1_struct_0(A_23), k3_relset_1(u1_struct_0(A_23), u1_struct_0(A_23), u1_orders_2(A_23)))=k7_lattice3(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.22  tff(c_6, plain, (![C_6, A_2, D_7, B_3]: (C_6=A_2 | g1_orders_2(C_6, D_7)!=g1_orders_2(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k2_zfmisc_1(A_2, A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.89/1.22  tff(c_66, plain, (![A_24, A_25, B_26]: (u1_struct_0(A_24)=A_25 | k7_lattice3(A_24)!=g1_orders_2(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~l1_orders_2(A_24))), inference(superposition, [status(thm), theory('equality')], [c_49, c_6])).
% 1.89/1.22  tff(c_70, plain, (![A_24, A_10]: (u1_struct_0(A_24)=u1_struct_0(A_10) | k7_lattice3(k7_lattice3(A_10))!=k7_lattice3(A_24) | ~m1_subset_1(u1_orders_2(A_10), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_10), u1_struct_0(A_10)))) | ~l1_orders_2(A_24) | ~l1_orders_2(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_66])).
% 1.89/1.22  tff(c_105, plain, (![A_47]: (u1_struct_0(k7_lattice3(A_47))=u1_struct_0(A_47) | ~m1_subset_1(u1_orders_2(A_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(A_47)))) | ~l1_orders_2(k7_lattice3(A_47)) | ~l1_orders_2(A_47))), inference(reflexivity, [status(thm), theory('equality')], [c_70])).
% 1.89/1.22  tff(c_110, plain, (![A_48]: (u1_struct_0(k7_lattice3(A_48))=u1_struct_0(A_48) | ~l1_orders_2(k7_lattice3(A_48)) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_2, c_105])).
% 1.89/1.22  tff(c_115, plain, (![A_49]: (u1_struct_0(k7_lattice3(A_49))=u1_struct_0(A_49) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_10, c_110])).
% 1.89/1.22  tff(c_16, plain, (u1_struct_0(k7_lattice3('#skF_1'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.22  tff(c_139, plain, (~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_115, c_16])).
% 1.89/1.22  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_139])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 3
% 1.89/1.22  #Sup     : 37
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 2
% 1.89/1.22  #Demod        : 1
% 1.89/1.22  #Tautology    : 7
% 1.89/1.22  #SimpNegUnit  : 0
% 1.89/1.22  #BackRed      : 0
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.28
% 1.89/1.22  Parsing              : 0.15
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.20
% 1.89/1.22  Inferencing          : 0.08
% 1.89/1.22  Reduction            : 0.04
% 1.89/1.22  Demodulation         : 0.03
% 1.89/1.22  BG Simplification    : 0.01
% 1.89/1.22  Subsumption          : 0.05
% 1.89/1.22  Abstraction          : 0.01
% 1.89/1.22  MUC search           : 0.00
% 1.89/1.22  Cooper               : 0.00
% 1.89/1.22  Total                : 0.50
% 1.89/1.22  Index Insertion      : 0.00
% 1.89/1.22  Index Deletion       : 0.00
% 1.89/1.22  Index Matching       : 0.00
% 1.89/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
