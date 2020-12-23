%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  68 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_18,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_10] :
      ( l1_orders_2(k7_lattice3(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10] :
      ( v1_orders_2(k7_lattice3(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_orders_2(A_2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(A_2))))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9] :
      ( g1_orders_2(u1_struct_0(A_9),k3_relset_1(u1_struct_0(A_9),u1_struct_0(A_9),u1_orders_2(A_9))) = k7_lattice3(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [C_16,A_17,D_18,B_19] :
      ( C_16 = A_17
      | g1_orders_2(C_16,D_18) != g1_orders_2(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [A_24,A_25,B_26] :
      ( u1_struct_0(A_24) = A_25
      | k7_lattice3(A_24) != g1_orders_2(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ l1_orders_2(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_131,plain,(
    ! [A_47,A_46] :
      ( u1_struct_0(A_47) = u1_struct_0(A_46)
      | k7_lattice3(A_46) != A_47
      | ~ m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ l1_orders_2(A_46)
      | ~ v1_orders_2(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_136,plain,(
    ! [A_49,A_48] :
      ( u1_struct_0(A_49) = u1_struct_0(A_48)
      | k7_lattice3(A_48) != A_49
      | ~ l1_orders_2(A_48)
      | ~ v1_orders_2(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_131])).

tff(c_144,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = u1_struct_0('#skF_1')
      | k7_lattice3('#skF_1') != A_50
      | ~ v1_orders_2(A_50)
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_18,c_136])).

tff(c_149,plain,(
    ! [A_51] :
      ( u1_struct_0(k7_lattice3(A_51)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_51) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(k7_lattice3(A_51))
      | ~ l1_orders_2(A_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_144])).

tff(c_154,plain,(
    ! [A_52] :
      ( u1_struct_0(k7_lattice3(A_52)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_52) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_52) ) ),
    inference(resolution,[status(thm)],[c_12,c_149])).

tff(c_16,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.34  
% 2.12/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.34  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1
% 2.12/1.34  
% 2.12/1.34  %Foreground sorts:
% 2.12/1.34  
% 2.12/1.34  
% 2.12/1.34  %Background operators:
% 2.12/1.34  
% 2.12/1.34  
% 2.12/1.34  %Foreground operators:
% 2.12/1.34  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.34  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 2.12/1.34  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.12/1.34  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 2.12/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.34  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.12/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.34  
% 2.12/1.35  tff(f_59, negated_conjecture, ~(![A]: (l1_orders_2(A) => (u1_struct_0(A) = u1_struct_0(k7_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow_6)).
% 2.12/1.35  tff(f_54, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(k7_lattice3(A)) & l1_orders_2(k7_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattice3)).
% 2.12/1.35  tff(f_35, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.12/1.35  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 2.12/1.35  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattice3)).
% 2.12/1.35  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 2.12/1.35  tff(c_18, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.35  tff(c_12, plain, (![A_10]: (l1_orders_2(k7_lattice3(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.35  tff(c_14, plain, (![A_10]: (v1_orders_2(k7_lattice3(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.35  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_orders_2(A_2), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2), u1_struct_0(A_2)))) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.35  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.35  tff(c_10, plain, (![A_9]: (g1_orders_2(u1_struct_0(A_9), k3_relset_1(u1_struct_0(A_9), u1_struct_0(A_9), u1_orders_2(A_9)))=k7_lattice3(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.35  tff(c_44, plain, (![C_16, A_17, D_18, B_19]: (C_16=A_17 | g1_orders_2(C_16, D_18)!=g1_orders_2(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.35  tff(c_66, plain, (![A_24, A_25, B_26]: (u1_struct_0(A_24)=A_25 | k7_lattice3(A_24)!=g1_orders_2(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~l1_orders_2(A_24))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 2.12/1.35  tff(c_131, plain, (![A_47, A_46]: (u1_struct_0(A_47)=u1_struct_0(A_46) | k7_lattice3(A_46)!=A_47 | ~m1_subset_1(u1_orders_2(A_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(A_47)))) | ~l1_orders_2(A_46) | ~v1_orders_2(A_47) | ~l1_orders_2(A_47))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.12/1.35  tff(c_136, plain, (![A_49, A_48]: (u1_struct_0(A_49)=u1_struct_0(A_48) | k7_lattice3(A_48)!=A_49 | ~l1_orders_2(A_48) | ~v1_orders_2(A_49) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_4, c_131])).
% 2.12/1.35  tff(c_144, plain, (![A_50]: (u1_struct_0(A_50)=u1_struct_0('#skF_1') | k7_lattice3('#skF_1')!=A_50 | ~v1_orders_2(A_50) | ~l1_orders_2(A_50))), inference(resolution, [status(thm)], [c_18, c_136])).
% 2.12/1.35  tff(c_149, plain, (![A_51]: (u1_struct_0(k7_lattice3(A_51))=u1_struct_0('#skF_1') | k7_lattice3(A_51)!=k7_lattice3('#skF_1') | ~l1_orders_2(k7_lattice3(A_51)) | ~l1_orders_2(A_51))), inference(resolution, [status(thm)], [c_14, c_144])).
% 2.12/1.35  tff(c_154, plain, (![A_52]: (u1_struct_0(k7_lattice3(A_52))=u1_struct_0('#skF_1') | k7_lattice3(A_52)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_52))), inference(resolution, [status(thm)], [c_12, c_149])).
% 2.12/1.35  tff(c_16, plain, (u1_struct_0(k7_lattice3('#skF_1'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.35  tff(c_178, plain, (~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 2.12/1.35  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_178])).
% 2.12/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.35  
% 2.12/1.35  Inference rules
% 2.12/1.35  ----------------------
% 2.12/1.35  #Ref     : 6
% 2.12/1.35  #Sup     : 40
% 2.12/1.35  #Fact    : 0
% 2.12/1.35  #Define  : 0
% 2.12/1.35  #Split   : 0
% 2.12/1.35  #Chain   : 0
% 2.12/1.35  #Close   : 0
% 2.12/1.35  
% 2.12/1.35  Ordering : KBO
% 2.12/1.35  
% 2.12/1.35  Simplification rules
% 2.12/1.35  ----------------------
% 2.12/1.35  #Subsume      : 2
% 2.12/1.35  #Demod        : 1
% 2.12/1.35  #Tautology    : 11
% 2.12/1.35  #SimpNegUnit  : 0
% 2.12/1.35  #BackRed      : 0
% 2.12/1.35  
% 2.12/1.35  #Partial instantiations: 0
% 2.12/1.35  #Strategies tried      : 1
% 2.12/1.35  
% 2.12/1.35  Timing (in seconds)
% 2.12/1.35  ----------------------
% 2.12/1.36  Preprocessing        : 0.31
% 2.12/1.36  Parsing              : 0.16
% 2.12/1.36  CNF conversion       : 0.02
% 2.12/1.36  Main loop            : 0.24
% 2.12/1.36  Inferencing          : 0.09
% 2.12/1.36  Reduction            : 0.06
% 2.12/1.36  Demodulation         : 0.04
% 2.12/1.36  BG Simplification    : 0.02
% 2.12/1.36  Subsumption          : 0.06
% 2.12/1.36  Abstraction          : 0.01
% 2.12/1.36  MUC search           : 0.00
% 2.12/1.36  Cooper               : 0.00
% 2.12/1.36  Total                : 0.59
% 2.12/1.36  Index Insertion      : 0.00
% 2.12/1.36  Index Deletion       : 0.00
% 2.12/1.36  Index Matching       : 0.00
% 2.12/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
