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
% DateTime   : Thu Dec  3 10:30:44 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 108 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k4_relat_1 > k1_zfmisc_1 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(c_22,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_17] :
      ( g1_orders_2(u1_struct_0(A_17),k3_relset_1(u1_struct_0(A_17),u1_struct_0(A_17),u1_orders_2(A_17))) = k7_lattice3(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_orders_2(A_10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_10),u1_struct_0(A_10))))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k3_relset_1(A_40,B_41,C_42),k1_zfmisc_1(k2_zfmisc_1(B_41,A_40)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( l1_orders_2(g1_orders_2(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,(
    ! [A_45,C_46] :
      ( l1_orders_2(g1_orders_2(A_45,k3_relset_1(A_45,A_45,C_46)))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_162,plain,(
    ! [A_49] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_49),k3_relset_1(u1_struct_0(A_49),u1_struct_0(A_49),u1_orders_2(A_49))))
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_165,plain,(
    ! [A_17] :
      ( l1_orders_2(k7_lattice3(A_17))
      | ~ l1_orders_2(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_162])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_orders_2(g1_orders_2(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [A_43,C_44] :
      ( v1_orders_2(g1_orders_2(A_43,k3_relset_1(A_43,A_43,C_44)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ) ),
    inference(resolution,[status(thm)],[c_120,c_10])).

tff(c_154,plain,(
    ! [A_47] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_47),k3_relset_1(u1_struct_0(A_47),u1_struct_0(A_47),u1_orders_2(A_47))))
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_157,plain,(
    ! [A_17] :
      ( v1_orders_2(k7_lattice3(A_17))
      | ~ l1_orders_2(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_154])).

tff(c_6,plain,(
    ! [A_7] :
      ( g1_orders_2(u1_struct_0(A_7),u1_orders_2(A_7)) = A_7
      | ~ v1_orders_2(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [C_29,A_30,D_31,B_32] :
      ( C_29 = A_30
      | g1_orders_2(C_29,D_31) != g1_orders_2(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_257,plain,(
    ! [A_76,C_77,D_78] :
      ( u1_struct_0(A_76) = C_77
      | g1_orders_2(C_77,D_78) != A_76
      | ~ m1_subset_1(u1_orders_2(A_76),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_76),u1_struct_0(A_76))))
      | ~ v1_orders_2(A_76)
      | ~ l1_orders_2(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_327,plain,(
    ! [A_89,A_88] :
      ( u1_struct_0(A_89) = u1_struct_0(A_88)
      | k7_lattice3(A_89) != A_88
      | ~ m1_subset_1(u1_orders_2(A_88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88),u1_struct_0(A_88))))
      | ~ v1_orders_2(A_88)
      | ~ l1_orders_2(A_88)
      | ~ l1_orders_2(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_257])).

tff(c_332,plain,(
    ! [A_91,A_90] :
      ( u1_struct_0(A_91) = u1_struct_0(A_90)
      | k7_lattice3(A_90) != A_91
      | ~ v1_orders_2(A_91)
      | ~ l1_orders_2(A_90)
      | ~ l1_orders_2(A_91) ) ),
    inference(resolution,[status(thm)],[c_12,c_327])).

tff(c_348,plain,(
    ! [A_92,A_93] :
      ( u1_struct_0(k7_lattice3(A_92)) = u1_struct_0(A_93)
      | k7_lattice3(A_93) != k7_lattice3(A_92)
      | ~ l1_orders_2(A_93)
      | ~ l1_orders_2(k7_lattice3(A_92))
      | ~ l1_orders_2(A_92) ) ),
    inference(resolution,[status(thm)],[c_157,c_332])).

tff(c_367,plain,(
    ! [A_94] :
      ( u1_struct_0(k7_lattice3(A_94)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_94) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(k7_lattice3(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(resolution,[status(thm)],[c_22,c_348])).

tff(c_372,plain,(
    ! [A_95] :
      ( u1_struct_0(k7_lattice3(A_95)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_95) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_95) ) ),
    inference(resolution,[status(thm)],[c_165,c_367])).

tff(c_20,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_453,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_20])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.43  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k4_relat_1 > k1_zfmisc_1 > #skF_1
% 2.59/1.43  
% 2.59/1.43  %Foreground sorts:
% 2.59/1.43  
% 2.59/1.43  
% 2.59/1.43  %Background operators:
% 2.59/1.43  
% 2.59/1.43  
% 2.59/1.43  %Foreground operators:
% 2.59/1.43  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.43  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 2.59/1.43  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.59/1.43  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 2.59/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.43  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.59/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.43  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.59/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.43  
% 2.59/1.44  tff(f_67, negated_conjecture, ~(![A]: (l1_orders_2(A) => (u1_struct_0(A) = u1_struct_0(k7_lattice3(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow_6)).
% 2.59/1.44  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattice3)).
% 2.59/1.44  tff(f_49, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.59/1.44  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 2.59/1.44  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (v1_orders_2(g1_orders_2(A, B)) & l1_orders_2(g1_orders_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 2.59/1.44  tff(f_39, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 2.59/1.44  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 2.59/1.44  tff(c_22, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.44  tff(c_18, plain, (![A_17]: (g1_orders_2(u1_struct_0(A_17), k3_relset_1(u1_struct_0(A_17), u1_struct_0(A_17), u1_orders_2(A_17)))=k7_lattice3(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.44  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_orders_2(A_10), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_10), u1_struct_0(A_10)))) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.44  tff(c_120, plain, (![A_40, B_41, C_42]: (m1_subset_1(k3_relset_1(A_40, B_41, C_42), k1_zfmisc_1(k2_zfmisc_1(B_41, A_40))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.44  tff(c_8, plain, (![A_8, B_9]: (l1_orders_2(g1_orders_2(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.44  tff(c_146, plain, (![A_45, C_46]: (l1_orders_2(g1_orders_2(A_45, k3_relset_1(A_45, A_45, C_46))) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(resolution, [status(thm)], [c_120, c_8])).
% 2.59/1.44  tff(c_162, plain, (![A_49]: (l1_orders_2(g1_orders_2(u1_struct_0(A_49), k3_relset_1(u1_struct_0(A_49), u1_struct_0(A_49), u1_orders_2(A_49)))) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_12, c_146])).
% 2.59/1.44  tff(c_165, plain, (![A_17]: (l1_orders_2(k7_lattice3(A_17)) | ~l1_orders_2(A_17) | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_162])).
% 2.59/1.44  tff(c_10, plain, (![A_8, B_9]: (v1_orders_2(g1_orders_2(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.59/1.44  tff(c_138, plain, (![A_43, C_44]: (v1_orders_2(g1_orders_2(A_43, k3_relset_1(A_43, A_43, C_44))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(resolution, [status(thm)], [c_120, c_10])).
% 2.59/1.44  tff(c_154, plain, (![A_47]: (v1_orders_2(g1_orders_2(u1_struct_0(A_47), k3_relset_1(u1_struct_0(A_47), u1_struct_0(A_47), u1_orders_2(A_47)))) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_12, c_138])).
% 2.59/1.44  tff(c_157, plain, (![A_17]: (v1_orders_2(k7_lattice3(A_17)) | ~l1_orders_2(A_17) | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_154])).
% 2.59/1.44  tff(c_6, plain, (![A_7]: (g1_orders_2(u1_struct_0(A_7), u1_orders_2(A_7))=A_7 | ~v1_orders_2(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.44  tff(c_60, plain, (![C_29, A_30, D_31, B_32]: (C_29=A_30 | g1_orders_2(C_29, D_31)!=g1_orders_2(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.59/1.44  tff(c_257, plain, (![A_76, C_77, D_78]: (u1_struct_0(A_76)=C_77 | g1_orders_2(C_77, D_78)!=A_76 | ~m1_subset_1(u1_orders_2(A_76), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_76), u1_struct_0(A_76)))) | ~v1_orders_2(A_76) | ~l1_orders_2(A_76))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.59/1.44  tff(c_327, plain, (![A_89, A_88]: (u1_struct_0(A_89)=u1_struct_0(A_88) | k7_lattice3(A_89)!=A_88 | ~m1_subset_1(u1_orders_2(A_88), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_88), u1_struct_0(A_88)))) | ~v1_orders_2(A_88) | ~l1_orders_2(A_88) | ~l1_orders_2(A_89))), inference(superposition, [status(thm), theory('equality')], [c_18, c_257])).
% 2.59/1.44  tff(c_332, plain, (![A_91, A_90]: (u1_struct_0(A_91)=u1_struct_0(A_90) | k7_lattice3(A_90)!=A_91 | ~v1_orders_2(A_91) | ~l1_orders_2(A_90) | ~l1_orders_2(A_91))), inference(resolution, [status(thm)], [c_12, c_327])).
% 2.59/1.44  tff(c_348, plain, (![A_92, A_93]: (u1_struct_0(k7_lattice3(A_92))=u1_struct_0(A_93) | k7_lattice3(A_93)!=k7_lattice3(A_92) | ~l1_orders_2(A_93) | ~l1_orders_2(k7_lattice3(A_92)) | ~l1_orders_2(A_92))), inference(resolution, [status(thm)], [c_157, c_332])).
% 2.59/1.44  tff(c_367, plain, (![A_94]: (u1_struct_0(k7_lattice3(A_94))=u1_struct_0('#skF_1') | k7_lattice3(A_94)!=k7_lattice3('#skF_1') | ~l1_orders_2(k7_lattice3(A_94)) | ~l1_orders_2(A_94))), inference(resolution, [status(thm)], [c_22, c_348])).
% 2.59/1.44  tff(c_372, plain, (![A_95]: (u1_struct_0(k7_lattice3(A_95))=u1_struct_0('#skF_1') | k7_lattice3(A_95)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_95))), inference(resolution, [status(thm)], [c_165, c_367])).
% 2.59/1.44  tff(c_20, plain, (u1_struct_0(k7_lattice3('#skF_1'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.44  tff(c_453, plain, (~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_372, c_20])).
% 2.59/1.44  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_453])).
% 2.59/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.44  
% 2.59/1.44  Inference rules
% 2.59/1.44  ----------------------
% 2.59/1.44  #Ref     : 6
% 2.59/1.44  #Sup     : 120
% 2.59/1.44  #Fact    : 0
% 2.59/1.44  #Define  : 0
% 2.59/1.44  #Split   : 0
% 2.59/1.44  #Chain   : 0
% 2.59/1.44  #Close   : 0
% 2.59/1.44  
% 2.59/1.44  Ordering : KBO
% 2.59/1.44  
% 2.59/1.44  Simplification rules
% 2.59/1.44  ----------------------
% 2.59/1.44  #Subsume      : 7
% 2.59/1.44  #Demod        : 1
% 2.59/1.44  #Tautology    : 17
% 2.59/1.44  #SimpNegUnit  : 0
% 2.59/1.44  #BackRed      : 0
% 2.59/1.44  
% 2.59/1.44  #Partial instantiations: 0
% 2.59/1.44  #Strategies tried      : 1
% 2.59/1.44  
% 2.59/1.44  Timing (in seconds)
% 2.59/1.44  ----------------------
% 2.59/1.44  Preprocessing        : 0.32
% 2.59/1.44  Parsing              : 0.17
% 2.59/1.44  CNF conversion       : 0.02
% 2.59/1.44  Main loop            : 0.31
% 2.59/1.44  Inferencing          : 0.13
% 2.59/1.44  Reduction            : 0.07
% 2.59/1.44  Demodulation         : 0.05
% 2.59/1.44  BG Simplification    : 0.02
% 2.59/1.44  Subsumption          : 0.07
% 2.59/1.44  Abstraction          : 0.02
% 2.59/1.44  MUC search           : 0.00
% 2.59/1.44  Cooper               : 0.00
% 2.59/1.44  Total                : 0.66
% 2.59/1.44  Index Insertion      : 0.00
% 2.59/1.44  Index Deletion       : 0.00
% 2.59/1.44  Index Matching       : 0.00
% 2.59/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
