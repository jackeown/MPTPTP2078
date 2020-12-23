%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:38 EST 2020

% Result     : Theorem 20.19s
% Output     : CNFRefutation 20.29s
% Verified   : 
% Statistics : Number of formulae       :  143 (32807 expanded)
%              Number of leaves         :   22 (10896 expanded)
%              Depth                    :   29
%              Number of atoms          :  352 (87302 expanded)
%              Number of equality atoms :  141 (24519 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,k3_relset_1(A,B,C)) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

tff(c_20,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

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

tff(c_96,plain,(
    ! [A_38,B_39,C_40] :
      ( m1_subset_1(k3_relset_1(A_38,B_39,C_40),k1_zfmisc_1(k2_zfmisc_1(B_39,A_38)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( l1_orders_2(g1_orders_2(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [A_43,C_44] :
      ( l1_orders_2(g1_orders_2(A_43,k3_relset_1(A_43,A_43,C_44)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ) ),
    inference(resolution,[status(thm)],[c_96,c_8])).

tff(c_131,plain,(
    ! [A_47] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_47),k3_relset_1(u1_struct_0(A_47),u1_struct_0(A_47),u1_orders_2(A_47))))
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_134,plain,(
    ! [A_17] :
      ( l1_orders_2(k7_lattice3(A_17))
      | ~ l1_orders_2(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_131])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_orders_2(g1_orders_2(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k2_zfmisc_1(A_8,A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [A_41,C_42] :
      ( v1_orders_2(g1_orders_2(A_41,k3_relset_1(A_41,A_41,C_42)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_126,plain,(
    ! [A_45] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_45),k3_relset_1(u1_struct_0(A_45),u1_struct_0(A_45),u1_orders_2(A_45))))
      | ~ l1_orders_2(A_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_129,plain,(
    ! [A_17] :
      ( v1_orders_2(k7_lattice3(A_17))
      | ~ l1_orders_2(A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_6,plain,(
    ! [A_7] :
      ( g1_orders_2(u1_struct_0(A_7),u1_orders_2(A_7)) = A_7
      | ~ v1_orders_2(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [D_34,B_35,C_36,A_37] :
      ( D_34 = B_35
      | g1_orders_2(C_36,D_34) != g1_orders_2(A_37,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_213,plain,(
    ! [A_67,D_68,C_69] :
      ( u1_orders_2(A_67) = D_68
      | g1_orders_2(C_69,D_68) != A_67
      | ~ m1_subset_1(u1_orders_2(A_67),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_67),u1_struct_0(A_67))))
      | ~ v1_orders_2(A_67)
      | ~ l1_orders_2(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_2617,plain,(
    ! [A_165,A_166] :
      ( u1_orders_2(A_165) = k3_relset_1(u1_struct_0(A_166),u1_struct_0(A_166),u1_orders_2(A_166))
      | k7_lattice3(A_166) != A_165
      | ~ m1_subset_1(u1_orders_2(A_165),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(A_165))))
      | ~ v1_orders_2(A_165)
      | ~ l1_orders_2(A_165)
      | ~ l1_orders_2(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_213])).

tff(c_2697,plain,(
    ! [A_168,A_169] :
      ( u1_orders_2(A_168) = k3_relset_1(u1_struct_0(A_169),u1_struct_0(A_169),u1_orders_2(A_169))
      | k7_lattice3(A_169) != A_168
      | ~ v1_orders_2(A_168)
      | ~ l1_orders_2(A_169)
      | ~ l1_orders_2(A_168) ) ),
    inference(resolution,[status(thm)],[c_12,c_2617])).

tff(c_3233,plain,(
    ! [A_175,A_176] :
      ( u1_orders_2(k7_lattice3(A_175)) = k3_relset_1(u1_struct_0(A_176),u1_struct_0(A_176),u1_orders_2(A_176))
      | k7_lattice3(A_176) != k7_lattice3(A_175)
      | ~ l1_orders_2(A_176)
      | ~ l1_orders_2(k7_lattice3(A_175))
      | ~ l1_orders_2(A_175) ) ),
    inference(resolution,[status(thm)],[c_129,c_2697])).

tff(c_3237,plain,(
    ! [A_177,A_178] :
      ( u1_orders_2(k7_lattice3(A_177)) = k3_relset_1(u1_struct_0(A_178),u1_struct_0(A_178),u1_orders_2(A_178))
      | k7_lattice3(A_178) != k7_lattice3(A_177)
      | ~ l1_orders_2(A_178)
      | ~ l1_orders_2(A_177) ) ),
    inference(resolution,[status(thm)],[c_134,c_3233])).

tff(c_3730,plain,(
    ! [A_185,A_186] :
      ( g1_orders_2(u1_struct_0(A_185),u1_orders_2(k7_lattice3(A_186))) = k7_lattice3(A_185)
      | ~ l1_orders_2(A_185)
      | k7_lattice3(A_186) != k7_lattice3(A_185)
      | ~ l1_orders_2(A_185)
      | ~ l1_orders_2(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3237,c_18])).

tff(c_74,plain,(
    ! [C_30,A_31,D_32,B_33] :
      ( C_30 = A_31
      | g1_orders_2(C_30,D_32) != g1_orders_2(A_31,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_49,A_50,B_51] :
      ( u1_struct_0(A_49) = A_50
      | k7_lattice3(A_49) != g1_orders_2(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_zfmisc_1(A_50,A_50)))
      | ~ l1_orders_2(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_244,plain,(
    ! [A_80,A_79] :
      ( u1_struct_0(A_80) = u1_struct_0(A_79)
      | k7_lattice3(A_80) != A_79
      | ~ m1_subset_1(u1_orders_2(A_79),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79),u1_struct_0(A_79))))
      | ~ l1_orders_2(A_80)
      | ~ v1_orders_2(A_79)
      | ~ l1_orders_2(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_136])).

tff(c_249,plain,(
    ! [A_82,A_81] :
      ( u1_struct_0(A_82) = u1_struct_0(A_81)
      | k7_lattice3(A_81) != A_82
      | ~ l1_orders_2(A_81)
      | ~ v1_orders_2(A_82)
      | ~ l1_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_244])).

tff(c_271,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = u1_struct_0('#skF_1')
      | k7_lattice3('#skF_1') != A_86
      | ~ v1_orders_2(A_86)
      | ~ l1_orders_2(A_86) ) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_288,plain,(
    ! [A_87] :
      ( u1_struct_0(k7_lattice3(A_87)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_87) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(k7_lattice3(A_87))
      | ~ l1_orders_2(A_87) ) ),
    inference(resolution,[status(thm)],[c_129,c_271])).

tff(c_293,plain,(
    ! [A_88] :
      ( u1_struct_0(k7_lattice3(A_88)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_88) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_88) ) ),
    inference(resolution,[status(thm)],[c_134,c_288])).

tff(c_40,plain,(
    ! [A_23] :
      ( m1_subset_1(u1_orders_2(A_23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_23),u1_struct_0(A_23))))
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_47,plain,(
    ! [A_23] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_23),u1_orders_2(A_23)))
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_40,c_10])).

tff(c_341,plain,(
    ! [A_88] :
      ( v1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_88))))
      | ~ l1_orders_2(k7_lattice3(A_88))
      | k7_lattice3(A_88) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_47])).

tff(c_3868,plain,(
    ! [A_186] :
      ( v1_orders_2(k7_lattice3('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_186))
      | k7_lattice3(A_186) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_186)
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_186) != k7_lattice3('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3730,c_341])).

tff(c_3975,plain,(
    ! [A_186] :
      ( v1_orders_2(k7_lattice3('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_186))
      | k7_lattice3(A_186) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_3868])).

tff(c_3984,plain,(
    ! [A_187] :
      ( ~ l1_orders_2(k7_lattice3(A_187))
      | k7_lattice3(A_187) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_187) ) ),
    inference(splitLeft,[status(thm)],[c_3975])).

tff(c_3989,plain,(
    ! [A_188] :
      ( k7_lattice3(A_188) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_188) ) ),
    inference(resolution,[status(thm)],[c_134,c_3984])).

tff(c_4030,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_3989])).

tff(c_4031,plain,(
    v1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3975])).

tff(c_264,plain,(
    ! [A_82] :
      ( u1_struct_0(A_82) = u1_struct_0('#skF_1')
      | k7_lattice3('#skF_1') != A_82
      | ~ v1_orders_2(A_82)
      | ~ l1_orders_2(A_82) ) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_4044,plain,
    ( u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0('#skF_1')
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4031,c_264])).

tff(c_4045,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4044])).

tff(c_4048,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_4045])).

tff(c_4052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4048])).

tff(c_4054,plain,(
    l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4044])).

tff(c_4053,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4044])).

tff(c_4328,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_18])).

tff(c_4485,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053,c_4053,c_4328])).

tff(c_125,plain,(
    ! [A_10] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_10),k3_relset_1(u1_struct_0(A_10),u1_struct_0(A_10),u1_orders_2(A_10))))
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_4310,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_125])).

tff(c_4473,plain,(
    l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053,c_4053,c_4310])).

tff(c_5421,plain,(
    l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4485,c_4473])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k3_relset_1(A_1,B_2,C_3),k1_zfmisc_1(k2_zfmisc_1(B_2,A_1)))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1246,plain,(
    ! [A_138,A_137] :
      ( u1_struct_0(A_138) = u1_struct_0(A_137)
      | k7_lattice3(A_138) != k7_lattice3(A_137)
      | ~ m1_subset_1(k3_relset_1(u1_struct_0(A_138),u1_struct_0(A_138),u1_orders_2(A_138)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138),u1_struct_0(A_138))))
      | ~ l1_orders_2(A_137)
      | ~ l1_orders_2(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_136])).

tff(c_1299,plain,(
    ! [A_140,A_139] :
      ( u1_struct_0(A_140) = u1_struct_0(A_139)
      | k7_lattice3(A_140) != k7_lattice3(A_139)
      | ~ l1_orders_2(A_140)
      | ~ l1_orders_2(A_139)
      | ~ m1_subset_1(u1_orders_2(A_139),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139),u1_struct_0(A_139)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_1246])).

tff(c_1327,plain,(
    ! [A_141] :
      ( u1_struct_0(A_141) = u1_struct_0('#skF_1')
      | k7_lattice3(A_141) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_141)
      | ~ m1_subset_1(u1_orders_2(A_141),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(A_141)))) ) ),
    inference(resolution,[status(thm)],[c_22,c_1299])).

tff(c_1367,plain,(
    ! [A_10] :
      ( u1_struct_0(A_10) = u1_struct_0('#skF_1')
      | k7_lattice3(A_10) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_1327])).

tff(c_5466,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))) = u1_struct_0('#skF_1')
    | k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(resolution,[status(thm)],[c_5421,c_1367])).

tff(c_5491,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5466])).

tff(c_4346,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))) = k7_lattice3('#skF_1')
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_6])).

tff(c_4497,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))) = k7_lattice3('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4031,c_4346])).

tff(c_117,plain,(
    ! [A_10] :
      ( v1_orders_2(g1_orders_2(u1_struct_0(A_10),k3_relset_1(u1_struct_0(A_10),u1_struct_0(A_10),u1_orders_2(A_10))))
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_95,plain,(
    ! [A_7,D_34,C_36] :
      ( u1_orders_2(A_7) = D_34
      | g1_orders_2(C_36,D_34) != A_7
      | ~ m1_subset_1(u1_orders_2(A_7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(A_7))))
      | ~ v1_orders_2(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_4900,plain,(
    ! [C_192,D_193] :
      ( u1_orders_2(g1_orders_2(C_192,D_193)) = D_193
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(C_192,D_193)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(C_192,D_193)),u1_struct_0(g1_orders_2(C_192,D_193)))))
      | ~ v1_orders_2(g1_orders_2(C_192,D_193))
      | ~ l1_orders_2(g1_orders_2(C_192,D_193)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_95])).

tff(c_5347,plain,(
    ! [C_197,D_198] :
      ( u1_orders_2(g1_orders_2(C_197,D_198)) = D_198
      | ~ v1_orders_2(g1_orders_2(C_197,D_198))
      | ~ l1_orders_2(g1_orders_2(C_197,D_198)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4900])).

tff(c_25893,plain,(
    ! [A_314] :
      ( u1_orders_2(g1_orders_2(u1_struct_0(A_314),k3_relset_1(u1_struct_0(A_314),u1_struct_0(A_314),u1_orders_2(A_314)))) = k3_relset_1(u1_struct_0(A_314),u1_struct_0(A_314),u1_orders_2(A_314))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_314),k3_relset_1(u1_struct_0(A_314),u1_struct_0(A_314),u1_orders_2(A_314))))
      | ~ l1_orders_2(A_314) ) ),
    inference(resolution,[status(thm)],[c_117,c_5347])).

tff(c_26157,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')),k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1'))))) = k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_25893])).

tff(c_26321,plain,(
    k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))) = u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_5421,c_4485,c_4053,c_4053,c_4053,c_4053,c_4485,c_4053,c_4053,c_4053,c_26157])).

tff(c_66,plain,(
    ! [A_27,B_28,C_29] :
      ( k3_relset_1(A_27,B_28,k3_relset_1(A_27,B_28,C_29)) = C_29
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_10] :
      ( k3_relset_1(u1_struct_0(A_10),u1_struct_0(A_10),k3_relset_1(u1_struct_0(A_10),u1_struct_0(A_10),u1_orders_2(A_10))) = u1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_4298,plain,
    ( k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))) = u1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_69])).

tff(c_4465,plain,(
    k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1')))) = u1_orders_2(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053,c_4053,c_4053,c_4298])).

tff(c_26327,plain,(
    k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) = u1_orders_2(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26321,c_4465])).

tff(c_4319,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4053,c_117])).

tff(c_4479,plain,(
    v1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053,c_4053,c_4319])).

tff(c_5422,plain,(
    v1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4485,c_4479])).

tff(c_247,plain,(
    ! [A_80,A_10] :
      ( u1_struct_0(A_80) = u1_struct_0(A_10)
      | k7_lattice3(A_80) != A_10
      | ~ l1_orders_2(A_80)
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_244])).

tff(c_4064,plain,(
    ! [A_10] :
      ( u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0(A_10)
      | k7_lattice3(k7_lattice3('#skF_1')) != A_10
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_4054,c_247])).

tff(c_5414,plain,(
    ! [A_10] :
      ( u1_struct_0(A_10) = u1_struct_0('#skF_1')
      | k7_lattice3(k7_lattice3('#skF_1')) != A_10
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4053,c_4064])).

tff(c_5418,plain,
    ( u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5414])).

tff(c_5582,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_5422,c_5418])).

tff(c_5765,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))),u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5582,c_18])).

tff(c_5931,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_5582,c_5582,c_5765])).

tff(c_27085,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1'))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26327,c_5931])).

tff(c_27086,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) = k7_lattice3('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4497,c_27085])).

tff(c_27088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5491,c_27086])).

tff(c_27090,plain,(
    k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) = k7_lattice3('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_27089,plain,(
    u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_27273,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))),u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27089,c_18])).

tff(c_27440,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))) = k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_27089,c_27089,c_27273])).

tff(c_34045,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))) = k7_lattice3('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27090,c_27440])).

tff(c_5003,plain,(
    ! [C_192,D_193] :
      ( u1_orders_2(g1_orders_2(C_192,D_193)) = D_193
      | ~ v1_orders_2(g1_orders_2(C_192,D_193))
      | ~ l1_orders_2(g1_orders_2(C_192,D_193)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4900])).

tff(c_34055,plain,
    ( u1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34045,c_5003])).

tff(c_34089,plain,(
    k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) = u1_orders_2(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_34045,c_4031,c_34045,c_34055])).

tff(c_238,plain,(
    ! [A_76,B_77,A_78] :
      ( k3_relset_1(u1_struct_0(A_76),u1_struct_0(A_76),u1_orders_2(A_76)) = B_77
      | k7_lattice3(A_76) != g1_orders_2(A_78,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(A_78,A_78)))
      | ~ l1_orders_2(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_27849,plain,(
    ! [A_317,A_316] :
      ( k3_relset_1(u1_struct_0(A_317),u1_struct_0(A_317),u1_orders_2(A_317)) = k3_relset_1(u1_struct_0(A_316),u1_struct_0(A_316),u1_orders_2(A_316))
      | k7_lattice3(A_317) != k7_lattice3(A_316)
      | ~ m1_subset_1(k3_relset_1(u1_struct_0(A_317),u1_struct_0(A_317),u1_orders_2(A_317)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_317),u1_struct_0(A_317))))
      | ~ l1_orders_2(A_316)
      | ~ l1_orders_2(A_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_238])).

tff(c_29339,plain,(
    ! [A_327,A_326] :
      ( k3_relset_1(u1_struct_0(A_327),u1_struct_0(A_327),u1_orders_2(A_327)) = k3_relset_1(u1_struct_0(A_326),u1_struct_0(A_326),u1_orders_2(A_326))
      | k7_lattice3(A_327) != k7_lattice3(A_326)
      | ~ l1_orders_2(A_327)
      | ~ l1_orders_2(A_326)
      | ~ m1_subset_1(u1_orders_2(A_326),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_326),u1_struct_0(A_326)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_27849])).

tff(c_35454,plain,(
    ! [A_380,A_379] :
      ( k3_relset_1(u1_struct_0(A_380),u1_struct_0(A_380),u1_orders_2(A_380)) = k3_relset_1(u1_struct_0(A_379),u1_struct_0(A_379),u1_orders_2(A_379))
      | k7_lattice3(A_380) != k7_lattice3(A_379)
      | ~ l1_orders_2(A_379)
      | ~ l1_orders_2(A_380) ) ),
    inference(resolution,[status(thm)],[c_12,c_29339])).

tff(c_35655,plain,(
    ! [A_379] :
      ( k3_relset_1(u1_struct_0(A_379),u1_struct_0(A_379),u1_orders_2(A_379)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))
      | k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) != k7_lattice3(A_379)
      | ~ l1_orders_2(A_379)
      | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27089,c_35454])).

tff(c_35861,plain,(
    ! [A_381] :
      ( k3_relset_1(u1_struct_0(A_381),u1_struct_0(A_381),u1_orders_2(A_381)) = u1_orders_2(k7_lattice3('#skF_1'))
      | k7_lattice3(A_381) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_27090,c_34089,c_27089,c_35655])).

tff(c_51705,plain,(
    ! [A_462] :
      ( k3_relset_1(u1_struct_0(A_462),u1_struct_0(A_462),u1_orders_2(k7_lattice3('#skF_1'))) = u1_orders_2(A_462)
      | ~ l1_orders_2(A_462)
      | k7_lattice3(A_462) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35861,c_69])).

tff(c_292,plain,(
    ! [A_17] :
      ( u1_struct_0(k7_lattice3(A_17)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_17) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_17) ) ),
    inference(resolution,[status(thm)],[c_134,c_288])).

tff(c_48,plain,(
    ! [A_23] :
      ( l1_orders_2(g1_orders_2(u1_struct_0(A_23),u1_orders_2(A_23)))
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_40,c_8])).

tff(c_93,plain,(
    ! [A_7,B_35,A_37] :
      ( u1_orders_2(A_7) = B_35
      | g1_orders_2(A_37,B_35) != A_7
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_37,A_37)))
      | ~ v1_orders_2(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_189,plain,(
    ! [A_63,B_64] :
      ( u1_orders_2(g1_orders_2(A_63,B_64)) = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_zfmisc_1(A_63,A_63)))
      | ~ v1_orders_2(g1_orders_2(A_63,B_64))
      | ~ l1_orders_2(g1_orders_2(A_63,B_64)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_93])).

tff(c_1824,plain,(
    ! [A_150] :
      ( u1_orders_2(g1_orders_2(u1_struct_0(A_150),u1_orders_2(A_150))) = u1_orders_2(A_150)
      | ~ v1_orders_2(g1_orders_2(u1_struct_0(A_150),u1_orders_2(A_150)))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_150),u1_orders_2(A_150)))
      | ~ l1_orders_2(A_150) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_1863,plain,(
    ! [A_151] :
      ( u1_orders_2(g1_orders_2(u1_struct_0(A_151),u1_orders_2(A_151))) = u1_orders_2(A_151)
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(A_151),u1_orders_2(A_151)))
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_47,c_1824])).

tff(c_1902,plain,(
    ! [A_152] :
      ( u1_orders_2(g1_orders_2(u1_struct_0(A_152),u1_orders_2(A_152))) = u1_orders_2(A_152)
      | ~ l1_orders_2(A_152) ) ),
    inference(resolution,[status(thm)],[c_48,c_1863])).

tff(c_1979,plain,(
    ! [A_17] :
      ( u1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_17)))) = u1_orders_2(k7_lattice3(A_17))
      | ~ l1_orders_2(k7_lattice3(A_17))
      | k7_lattice3(A_17) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_1902])).

tff(c_3790,plain,(
    ! [A_186] :
      ( u1_orders_2(k7_lattice3(A_186)) = u1_orders_2(k7_lattice3('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_186))
      | k7_lattice3(A_186) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_186)
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_186) != k7_lattice3('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3730,c_1979])).

tff(c_29983,plain,(
    ! [A_333] :
      ( u1_orders_2(k7_lattice3(A_333)) = u1_orders_2(k7_lattice3('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_333))
      | k7_lattice3(A_333) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_3790])).

tff(c_30009,plain,(
    ! [A_17] :
      ( u1_orders_2(k7_lattice3(A_17)) = u1_orders_2(k7_lattice3('#skF_1'))
      | k7_lattice3(A_17) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_17) ) ),
    inference(resolution,[status(thm)],[c_134,c_29983])).

tff(c_2658,plain,(
    ! [A_10,A_166] :
      ( u1_orders_2(A_10) = k3_relset_1(u1_struct_0(A_166),u1_struct_0(A_166),u1_orders_2(A_166))
      | k7_lattice3(A_166) != A_10
      | ~ v1_orders_2(A_10)
      | ~ l1_orders_2(A_166)
      | ~ l1_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_2617])).

tff(c_5470,plain,(
    ! [A_166] :
      ( k3_relset_1(u1_struct_0(A_166),u1_struct_0(A_166),u1_orders_2(A_166)) = u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
      | k7_lattice3(k7_lattice3('#skF_1')) != k7_lattice3(A_166)
      | ~ l1_orders_2(A_166)
      | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_5422,c_2658])).

tff(c_47819,plain,(
    ! [A_435] :
      ( k3_relset_1(u1_struct_0(A_435),u1_struct_0(A_435),u1_orders_2(A_435)) = u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
      | k7_lattice3(k7_lattice3('#skF_1')) != k7_lattice3(A_435)
      | ~ l1_orders_2(A_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_5470])).

tff(c_48020,plain,(
    ! [A_17] :
      ( k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3(A_17))) = u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
      | ~ l1_orders_2(k7_lattice3('#skF_1'))
      | k7_lattice3(A_17) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30009,c_47819])).

tff(c_48130,plain,(
    ! [A_17] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_17))) = u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
      | k7_lattice3(A_17) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4053,c_4053,c_48020])).

tff(c_51725,plain,
    ( u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) = u1_orders_2('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51705,c_48130])).

tff(c_52046,plain,(
    u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) = u1_orders_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_51725])).

tff(c_27291,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1'))
    | ~ v1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_27089,c_6])).

tff(c_27452,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5421,c_5422,c_27291])).

tff(c_52432,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) = k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52046,c_27452])).

tff(c_52434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_52432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.19/9.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.29/9.80  
% 20.29/9.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.29/9.80  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1
% 20.29/9.80  
% 20.29/9.80  %Foreground sorts:
% 20.29/9.80  
% 20.29/9.80  
% 20.29/9.80  %Background operators:
% 20.29/9.80  
% 20.29/9.80  
% 20.29/9.80  %Foreground operators:
% 20.29/9.80  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 20.29/9.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.29/9.80  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 20.29/9.80  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 20.29/9.80  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 20.29/9.80  tff('#skF_1', type, '#skF_1': $i).
% 20.29/9.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.29/9.80  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 20.29/9.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.29/9.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.29/9.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.29/9.80  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 20.29/9.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.29/9.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.29/9.80  
% 20.29/9.83  tff(f_67, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_lattice3)).
% 20.29/9.83  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattice3)).
% 20.29/9.83  tff(f_49, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 20.29/9.83  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 20.29/9.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (v1_orders_2(g1_orders_2(A, B)) & l1_orders_2(g1_orders_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 20.29/9.83  tff(f_39, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 20.29/9.83  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 20.29/9.83  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, k3_relset_1(A, B, C)) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_relset_1)).
% 20.29/9.83  tff(c_20, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=k7_lattice3(k7_lattice3('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.29/9.83  tff(c_22, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 20.29/9.83  tff(c_18, plain, (![A_17]: (g1_orders_2(u1_struct_0(A_17), k3_relset_1(u1_struct_0(A_17), u1_struct_0(A_17), u1_orders_2(A_17)))=k7_lattice3(A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.29/9.83  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_orders_2(A_10), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_10), u1_struct_0(A_10)))) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.29/9.83  tff(c_96, plain, (![A_38, B_39, C_40]: (m1_subset_1(k3_relset_1(A_38, B_39, C_40), k1_zfmisc_1(k2_zfmisc_1(B_39, A_38))) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.29/9.83  tff(c_8, plain, (![A_8, B_9]: (l1_orders_2(g1_orders_2(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.29/9.83  tff(c_118, plain, (![A_43, C_44]: (l1_orders_2(g1_orders_2(A_43, k3_relset_1(A_43, A_43, C_44))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(resolution, [status(thm)], [c_96, c_8])).
% 20.29/9.83  tff(c_131, plain, (![A_47]: (l1_orders_2(g1_orders_2(u1_struct_0(A_47), k3_relset_1(u1_struct_0(A_47), u1_struct_0(A_47), u1_orders_2(A_47)))) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_12, c_118])).
% 20.29/9.83  tff(c_134, plain, (![A_17]: (l1_orders_2(k7_lattice3(A_17)) | ~l1_orders_2(A_17) | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_131])).
% 20.29/9.83  tff(c_10, plain, (![A_8, B_9]: (v1_orders_2(g1_orders_2(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(k2_zfmisc_1(A_8, A_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.29/9.83  tff(c_110, plain, (![A_41, C_42]: (v1_orders_2(g1_orders_2(A_41, k3_relset_1(A_41, A_41, C_42))) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(resolution, [status(thm)], [c_96, c_10])).
% 20.29/9.83  tff(c_126, plain, (![A_45]: (v1_orders_2(g1_orders_2(u1_struct_0(A_45), k3_relset_1(u1_struct_0(A_45), u1_struct_0(A_45), u1_orders_2(A_45)))) | ~l1_orders_2(A_45))), inference(resolution, [status(thm)], [c_12, c_110])).
% 20.29/9.83  tff(c_129, plain, (![A_17]: (v1_orders_2(k7_lattice3(A_17)) | ~l1_orders_2(A_17) | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_126])).
% 20.29/9.83  tff(c_6, plain, (![A_7]: (g1_orders_2(u1_struct_0(A_7), u1_orders_2(A_7))=A_7 | ~v1_orders_2(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.29/9.83  tff(c_87, plain, (![D_34, B_35, C_36, A_37]: (D_34=B_35 | g1_orders_2(C_36, D_34)!=g1_orders_2(A_37, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.29/9.83  tff(c_213, plain, (![A_67, D_68, C_69]: (u1_orders_2(A_67)=D_68 | g1_orders_2(C_69, D_68)!=A_67 | ~m1_subset_1(u1_orders_2(A_67), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_67), u1_struct_0(A_67)))) | ~v1_orders_2(A_67) | ~l1_orders_2(A_67))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 20.29/9.83  tff(c_2617, plain, (![A_165, A_166]: (u1_orders_2(A_165)=k3_relset_1(u1_struct_0(A_166), u1_struct_0(A_166), u1_orders_2(A_166)) | k7_lattice3(A_166)!=A_165 | ~m1_subset_1(u1_orders_2(A_165), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165), u1_struct_0(A_165)))) | ~v1_orders_2(A_165) | ~l1_orders_2(A_165) | ~l1_orders_2(A_166))), inference(superposition, [status(thm), theory('equality')], [c_18, c_213])).
% 20.29/9.83  tff(c_2697, plain, (![A_168, A_169]: (u1_orders_2(A_168)=k3_relset_1(u1_struct_0(A_169), u1_struct_0(A_169), u1_orders_2(A_169)) | k7_lattice3(A_169)!=A_168 | ~v1_orders_2(A_168) | ~l1_orders_2(A_169) | ~l1_orders_2(A_168))), inference(resolution, [status(thm)], [c_12, c_2617])).
% 20.29/9.83  tff(c_3233, plain, (![A_175, A_176]: (u1_orders_2(k7_lattice3(A_175))=k3_relset_1(u1_struct_0(A_176), u1_struct_0(A_176), u1_orders_2(A_176)) | k7_lattice3(A_176)!=k7_lattice3(A_175) | ~l1_orders_2(A_176) | ~l1_orders_2(k7_lattice3(A_175)) | ~l1_orders_2(A_175))), inference(resolution, [status(thm)], [c_129, c_2697])).
% 20.29/9.83  tff(c_3237, plain, (![A_177, A_178]: (u1_orders_2(k7_lattice3(A_177))=k3_relset_1(u1_struct_0(A_178), u1_struct_0(A_178), u1_orders_2(A_178)) | k7_lattice3(A_178)!=k7_lattice3(A_177) | ~l1_orders_2(A_178) | ~l1_orders_2(A_177))), inference(resolution, [status(thm)], [c_134, c_3233])).
% 20.29/9.83  tff(c_3730, plain, (![A_185, A_186]: (g1_orders_2(u1_struct_0(A_185), u1_orders_2(k7_lattice3(A_186)))=k7_lattice3(A_185) | ~l1_orders_2(A_185) | k7_lattice3(A_186)!=k7_lattice3(A_185) | ~l1_orders_2(A_185) | ~l1_orders_2(A_186))), inference(superposition, [status(thm), theory('equality')], [c_3237, c_18])).
% 20.29/9.83  tff(c_74, plain, (![C_30, A_31, D_32, B_33]: (C_30=A_31 | g1_orders_2(C_30, D_32)!=g1_orders_2(A_31, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.29/9.83  tff(c_136, plain, (![A_49, A_50, B_51]: (u1_struct_0(A_49)=A_50 | k7_lattice3(A_49)!=g1_orders_2(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))) | ~l1_orders_2(A_49))), inference(superposition, [status(thm), theory('equality')], [c_18, c_74])).
% 20.29/9.83  tff(c_244, plain, (![A_80, A_79]: (u1_struct_0(A_80)=u1_struct_0(A_79) | k7_lattice3(A_80)!=A_79 | ~m1_subset_1(u1_orders_2(A_79), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79), u1_struct_0(A_79)))) | ~l1_orders_2(A_80) | ~v1_orders_2(A_79) | ~l1_orders_2(A_79))), inference(superposition, [status(thm), theory('equality')], [c_6, c_136])).
% 20.29/9.83  tff(c_249, plain, (![A_82, A_81]: (u1_struct_0(A_82)=u1_struct_0(A_81) | k7_lattice3(A_81)!=A_82 | ~l1_orders_2(A_81) | ~v1_orders_2(A_82) | ~l1_orders_2(A_82))), inference(resolution, [status(thm)], [c_12, c_244])).
% 20.29/9.83  tff(c_271, plain, (![A_86]: (u1_struct_0(A_86)=u1_struct_0('#skF_1') | k7_lattice3('#skF_1')!=A_86 | ~v1_orders_2(A_86) | ~l1_orders_2(A_86))), inference(resolution, [status(thm)], [c_22, c_249])).
% 20.29/9.83  tff(c_288, plain, (![A_87]: (u1_struct_0(k7_lattice3(A_87))=u1_struct_0('#skF_1') | k7_lattice3(A_87)!=k7_lattice3('#skF_1') | ~l1_orders_2(k7_lattice3(A_87)) | ~l1_orders_2(A_87))), inference(resolution, [status(thm)], [c_129, c_271])).
% 20.29/9.83  tff(c_293, plain, (![A_88]: (u1_struct_0(k7_lattice3(A_88))=u1_struct_0('#skF_1') | k7_lattice3(A_88)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_88))), inference(resolution, [status(thm)], [c_134, c_288])).
% 20.29/9.83  tff(c_40, plain, (![A_23]: (m1_subset_1(u1_orders_2(A_23), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_23), u1_struct_0(A_23)))) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.29/9.83  tff(c_47, plain, (![A_23]: (v1_orders_2(g1_orders_2(u1_struct_0(A_23), u1_orders_2(A_23))) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_40, c_10])).
% 20.29/9.83  tff(c_341, plain, (![A_88]: (v1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_88)))) | ~l1_orders_2(k7_lattice3(A_88)) | k7_lattice3(A_88)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_88))), inference(superposition, [status(thm), theory('equality')], [c_293, c_47])).
% 20.29/9.83  tff(c_3868, plain, (![A_186]: (v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3(A_186)) | k7_lattice3(A_186)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_186) | ~l1_orders_2('#skF_1') | k7_lattice3(A_186)!=k7_lattice3('#skF_1') | ~l1_orders_2('#skF_1') | ~l1_orders_2(A_186))), inference(superposition, [status(thm), theory('equality')], [c_3730, c_341])).
% 20.29/9.83  tff(c_3975, plain, (![A_186]: (v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3(A_186)) | k7_lattice3(A_186)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_3868])).
% 20.29/9.83  tff(c_3984, plain, (![A_187]: (~l1_orders_2(k7_lattice3(A_187)) | k7_lattice3(A_187)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_187))), inference(splitLeft, [status(thm)], [c_3975])).
% 20.29/9.83  tff(c_3989, plain, (![A_188]: (k7_lattice3(A_188)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_188))), inference(resolution, [status(thm)], [c_134, c_3984])).
% 20.29/9.83  tff(c_4030, plain, $false, inference(resolution, [status(thm)], [c_22, c_3989])).
% 20.29/9.83  tff(c_4031, plain, (v1_orders_2(k7_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_3975])).
% 20.29/9.83  tff(c_264, plain, (![A_82]: (u1_struct_0(A_82)=u1_struct_0('#skF_1') | k7_lattice3('#skF_1')!=A_82 | ~v1_orders_2(A_82) | ~l1_orders_2(A_82))), inference(resolution, [status(thm)], [c_22, c_249])).
% 20.29/9.83  tff(c_4044, plain, (u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0('#skF_1') | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_4031, c_264])).
% 20.29/9.83  tff(c_4045, plain, (~l1_orders_2(k7_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_4044])).
% 20.29/9.83  tff(c_4048, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_134, c_4045])).
% 20.29/9.83  tff(c_4052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_4048])).
% 20.29/9.83  tff(c_4054, plain, (l1_orders_2(k7_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_4044])).
% 20.29/9.83  tff(c_4053, plain, (u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_4044])).
% 20.29/9.83  tff(c_4328, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_18])).
% 20.29/9.83  tff(c_4485, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053, c_4053, c_4328])).
% 20.29/9.83  tff(c_125, plain, (![A_10]: (l1_orders_2(g1_orders_2(u1_struct_0(A_10), k3_relset_1(u1_struct_0(A_10), u1_struct_0(A_10), u1_orders_2(A_10)))) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_118])).
% 20.29/9.83  tff(c_4310, plain, (l1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_125])).
% 20.29/9.83  tff(c_4473, plain, (l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053, c_4053, c_4310])).
% 20.29/9.83  tff(c_5421, plain, (l1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4485, c_4473])).
% 20.29/9.83  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k3_relset_1(A_1, B_2, C_3), k1_zfmisc_1(k2_zfmisc_1(B_2, A_1))) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.29/9.83  tff(c_1246, plain, (![A_138, A_137]: (u1_struct_0(A_138)=u1_struct_0(A_137) | k7_lattice3(A_138)!=k7_lattice3(A_137) | ~m1_subset_1(k3_relset_1(u1_struct_0(A_138), u1_struct_0(A_138), u1_orders_2(A_138)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138), u1_struct_0(A_138)))) | ~l1_orders_2(A_137) | ~l1_orders_2(A_138))), inference(superposition, [status(thm), theory('equality')], [c_18, c_136])).
% 20.29/9.83  tff(c_1299, plain, (![A_140, A_139]: (u1_struct_0(A_140)=u1_struct_0(A_139) | k7_lattice3(A_140)!=k7_lattice3(A_139) | ~l1_orders_2(A_140) | ~l1_orders_2(A_139) | ~m1_subset_1(u1_orders_2(A_139), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139), u1_struct_0(A_139)))))), inference(resolution, [status(thm)], [c_2, c_1246])).
% 20.29/9.83  tff(c_1327, plain, (![A_141]: (u1_struct_0(A_141)=u1_struct_0('#skF_1') | k7_lattice3(A_141)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_141) | ~m1_subset_1(u1_orders_2(A_141), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(A_141)))))), inference(resolution, [status(thm)], [c_22, c_1299])).
% 20.29/9.83  tff(c_1367, plain, (![A_10]: (u1_struct_0(A_10)=u1_struct_0('#skF_1') | k7_lattice3(A_10)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_1327])).
% 20.29/9.83  tff(c_5466, plain, (u1_struct_0(k7_lattice3(k7_lattice3('#skF_1')))=u1_struct_0('#skF_1') | k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))!=k7_lattice3('#skF_1')), inference(resolution, [status(thm)], [c_5421, c_1367])).
% 20.29/9.83  tff(c_5491, plain, (k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))!=k7_lattice3('#skF_1')), inference(splitLeft, [status(thm)], [c_5466])).
% 20.29/9.83  tff(c_4346, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))=k7_lattice3('#skF_1') | ~v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_6])).
% 20.29/9.83  tff(c_4497, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))=k7_lattice3('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4031, c_4346])).
% 20.29/9.83  tff(c_117, plain, (![A_10]: (v1_orders_2(g1_orders_2(u1_struct_0(A_10), k3_relset_1(u1_struct_0(A_10), u1_struct_0(A_10), u1_orders_2(A_10)))) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_110])).
% 20.29/9.83  tff(c_95, plain, (![A_7, D_34, C_36]: (u1_orders_2(A_7)=D_34 | g1_orders_2(C_36, D_34)!=A_7 | ~m1_subset_1(u1_orders_2(A_7), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7), u1_struct_0(A_7)))) | ~v1_orders_2(A_7) | ~l1_orders_2(A_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 20.29/9.83  tff(c_4900, plain, (![C_192, D_193]: (u1_orders_2(g1_orders_2(C_192, D_193))=D_193 | ~m1_subset_1(u1_orders_2(g1_orders_2(C_192, D_193)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(C_192, D_193)), u1_struct_0(g1_orders_2(C_192, D_193))))) | ~v1_orders_2(g1_orders_2(C_192, D_193)) | ~l1_orders_2(g1_orders_2(C_192, D_193)))), inference(reflexivity, [status(thm), theory('equality')], [c_95])).
% 20.29/9.83  tff(c_5347, plain, (![C_197, D_198]: (u1_orders_2(g1_orders_2(C_197, D_198))=D_198 | ~v1_orders_2(g1_orders_2(C_197, D_198)) | ~l1_orders_2(g1_orders_2(C_197, D_198)))), inference(resolution, [status(thm)], [c_12, c_4900])).
% 20.29/9.83  tff(c_25893, plain, (![A_314]: (u1_orders_2(g1_orders_2(u1_struct_0(A_314), k3_relset_1(u1_struct_0(A_314), u1_struct_0(A_314), u1_orders_2(A_314))))=k3_relset_1(u1_struct_0(A_314), u1_struct_0(A_314), u1_orders_2(A_314)) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_314), k3_relset_1(u1_struct_0(A_314), u1_struct_0(A_314), u1_orders_2(A_314)))) | ~l1_orders_2(A_314))), inference(resolution, [status(thm)], [c_117, c_5347])).
% 20.29/9.83  tff(c_26157, plain, (u1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')), k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1')))))=k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))) | ~l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_25893])).
% 20.29/9.83  tff(c_26321, plain, (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))=u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_5421, c_4485, c_4053, c_4053, c_4053, c_4053, c_4485, c_4053, c_4053, c_4053, c_26157])).
% 20.29/9.83  tff(c_66, plain, (![A_27, B_28, C_29]: (k3_relset_1(A_27, B_28, k3_relset_1(A_27, B_28, C_29))=C_29 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.29/9.83  tff(c_69, plain, (![A_10]: (k3_relset_1(u1_struct_0(A_10), u1_struct_0(A_10), k3_relset_1(u1_struct_0(A_10), u1_struct_0(A_10), u1_orders_2(A_10)))=u1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_66])).
% 20.29/9.83  tff(c_4298, plain, (k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))=u1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_69])).
% 20.29/9.83  tff(c_4465, plain, (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1'))))=u1_orders_2(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053, c_4053, c_4053, c_4298])).
% 20.29/9.83  tff(c_26327, plain, (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))=u1_orders_2(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26321, c_4465])).
% 20.29/9.83  tff(c_4319, plain, (v1_orders_2(g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4053, c_117])).
% 20.29/9.83  tff(c_4479, plain, (v1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053, c_4053, c_4319])).
% 20.29/9.83  tff(c_5422, plain, (v1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4485, c_4479])).
% 20.29/9.83  tff(c_247, plain, (![A_80, A_10]: (u1_struct_0(A_80)=u1_struct_0(A_10) | k7_lattice3(A_80)!=A_10 | ~l1_orders_2(A_80) | ~v1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_244])).
% 20.29/9.83  tff(c_4064, plain, (![A_10]: (u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0(A_10) | k7_lattice3(k7_lattice3('#skF_1'))!=A_10 | ~v1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_4054, c_247])).
% 20.29/9.83  tff(c_5414, plain, (![A_10]: (u1_struct_0(A_10)=u1_struct_0('#skF_1') | k7_lattice3(k7_lattice3('#skF_1'))!=A_10 | ~v1_orders_2(A_10) | ~l1_orders_2(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_4053, c_4064])).
% 20.29/9.83  tff(c_5418, plain, (u1_struct_0(k7_lattice3(k7_lattice3('#skF_1')))=u1_struct_0('#skF_1') | ~v1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_5414])).
% 20.29/9.83  tff(c_5582, plain, (u1_struct_0(k7_lattice3(k7_lattice3('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_5422, c_5418])).
% 20.29/9.83  tff(c_5765, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))), u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))=k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5582, c_18])).
% 20.29/9.83  tff(c_5931, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))=k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_5582, c_5582, c_5765])).
% 20.29/9.83  tff(c_27085, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1')))=k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26327, c_5931])).
% 20.29/9.83  tff(c_27086, plain, (k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))=k7_lattice3('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4497, c_27085])).
% 20.29/9.83  tff(c_27088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5491, c_27086])).
% 20.29/9.83  tff(c_27090, plain, (k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))=k7_lattice3('#skF_1')), inference(splitRight, [status(thm)], [c_5466])).
% 20.29/9.83  tff(c_27089, plain, (u1_struct_0(k7_lattice3(k7_lattice3('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_5466])).
% 20.29/9.83  tff(c_27273, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))), u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))=k7_lattice3(k7_lattice3(k7_lattice3('#skF_1'))) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_27089, c_18])).
% 20.29/9.83  tff(c_27440, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))=k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_27089, c_27089, c_27273])).
% 20.29/9.83  tff(c_34045, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))))=k7_lattice3('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27090, c_27440])).
% 20.29/9.83  tff(c_5003, plain, (![C_192, D_193]: (u1_orders_2(g1_orders_2(C_192, D_193))=D_193 | ~v1_orders_2(g1_orders_2(C_192, D_193)) | ~l1_orders_2(g1_orders_2(C_192, D_193)))), inference(resolution, [status(thm)], [c_12, c_4900])).
% 20.29/9.83  tff(c_34055, plain, (u1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) | ~v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))))), inference(superposition, [status(thm), theory('equality')], [c_34045, c_5003])).
% 20.29/9.83  tff(c_34089, plain, (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))=u1_orders_2(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_34045, c_4031, c_34045, c_34055])).
% 20.29/9.83  tff(c_238, plain, (![A_76, B_77, A_78]: (k3_relset_1(u1_struct_0(A_76), u1_struct_0(A_76), u1_orders_2(A_76))=B_77 | k7_lattice3(A_76)!=g1_orders_2(A_78, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(A_78, A_78))) | ~l1_orders_2(A_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_87])).
% 20.29/9.83  tff(c_27849, plain, (![A_317, A_316]: (k3_relset_1(u1_struct_0(A_317), u1_struct_0(A_317), u1_orders_2(A_317))=k3_relset_1(u1_struct_0(A_316), u1_struct_0(A_316), u1_orders_2(A_316)) | k7_lattice3(A_317)!=k7_lattice3(A_316) | ~m1_subset_1(k3_relset_1(u1_struct_0(A_317), u1_struct_0(A_317), u1_orders_2(A_317)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_317), u1_struct_0(A_317)))) | ~l1_orders_2(A_316) | ~l1_orders_2(A_317))), inference(superposition, [status(thm), theory('equality')], [c_18, c_238])).
% 20.29/9.83  tff(c_29339, plain, (![A_327, A_326]: (k3_relset_1(u1_struct_0(A_327), u1_struct_0(A_327), u1_orders_2(A_327))=k3_relset_1(u1_struct_0(A_326), u1_struct_0(A_326), u1_orders_2(A_326)) | k7_lattice3(A_327)!=k7_lattice3(A_326) | ~l1_orders_2(A_327) | ~l1_orders_2(A_326) | ~m1_subset_1(u1_orders_2(A_326), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_326), u1_struct_0(A_326)))))), inference(resolution, [status(thm)], [c_2, c_27849])).
% 20.29/9.83  tff(c_35454, plain, (![A_380, A_379]: (k3_relset_1(u1_struct_0(A_380), u1_struct_0(A_380), u1_orders_2(A_380))=k3_relset_1(u1_struct_0(A_379), u1_struct_0(A_379), u1_orders_2(A_379)) | k7_lattice3(A_380)!=k7_lattice3(A_379) | ~l1_orders_2(A_379) | ~l1_orders_2(A_380))), inference(resolution, [status(thm)], [c_12, c_29339])).
% 20.29/9.83  tff(c_35655, plain, (![A_379]: (k3_relset_1(u1_struct_0(A_379), u1_struct_0(A_379), u1_orders_2(A_379))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0(k7_lattice3(k7_lattice3('#skF_1'))), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))) | k7_lattice3(k7_lattice3(k7_lattice3('#skF_1')))!=k7_lattice3(A_379) | ~l1_orders_2(A_379) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_27089, c_35454])).
% 20.29/9.83  tff(c_35861, plain, (![A_381]: (k3_relset_1(u1_struct_0(A_381), u1_struct_0(A_381), u1_orders_2(A_381))=u1_orders_2(k7_lattice3('#skF_1')) | k7_lattice3(A_381)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_381))), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_27090, c_34089, c_27089, c_35655])).
% 20.29/9.83  tff(c_51705, plain, (![A_462]: (k3_relset_1(u1_struct_0(A_462), u1_struct_0(A_462), u1_orders_2(k7_lattice3('#skF_1')))=u1_orders_2(A_462) | ~l1_orders_2(A_462) | k7_lattice3(A_462)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_462))), inference(superposition, [status(thm), theory('equality')], [c_35861, c_69])).
% 20.29/9.83  tff(c_292, plain, (![A_17]: (u1_struct_0(k7_lattice3(A_17))=u1_struct_0('#skF_1') | k7_lattice3(A_17)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_17))), inference(resolution, [status(thm)], [c_134, c_288])).
% 20.29/9.83  tff(c_48, plain, (![A_23]: (l1_orders_2(g1_orders_2(u1_struct_0(A_23), u1_orders_2(A_23))) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_40, c_8])).
% 20.29/9.83  tff(c_93, plain, (![A_7, B_35, A_37]: (u1_orders_2(A_7)=B_35 | g1_orders_2(A_37, B_35)!=A_7 | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))) | ~v1_orders_2(A_7) | ~l1_orders_2(A_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 20.29/9.83  tff(c_189, plain, (![A_63, B_64]: (u1_orders_2(g1_orders_2(A_63, B_64))=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(k2_zfmisc_1(A_63, A_63))) | ~v1_orders_2(g1_orders_2(A_63, B_64)) | ~l1_orders_2(g1_orders_2(A_63, B_64)))), inference(reflexivity, [status(thm), theory('equality')], [c_93])).
% 20.29/9.83  tff(c_1824, plain, (![A_150]: (u1_orders_2(g1_orders_2(u1_struct_0(A_150), u1_orders_2(A_150)))=u1_orders_2(A_150) | ~v1_orders_2(g1_orders_2(u1_struct_0(A_150), u1_orders_2(A_150))) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_150), u1_orders_2(A_150))) | ~l1_orders_2(A_150))), inference(resolution, [status(thm)], [c_12, c_189])).
% 20.29/9.83  tff(c_1863, plain, (![A_151]: (u1_orders_2(g1_orders_2(u1_struct_0(A_151), u1_orders_2(A_151)))=u1_orders_2(A_151) | ~l1_orders_2(g1_orders_2(u1_struct_0(A_151), u1_orders_2(A_151))) | ~l1_orders_2(A_151))), inference(resolution, [status(thm)], [c_47, c_1824])).
% 20.29/9.83  tff(c_1902, plain, (![A_152]: (u1_orders_2(g1_orders_2(u1_struct_0(A_152), u1_orders_2(A_152)))=u1_orders_2(A_152) | ~l1_orders_2(A_152))), inference(resolution, [status(thm)], [c_48, c_1863])).
% 20.29/9.83  tff(c_1979, plain, (![A_17]: (u1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_17))))=u1_orders_2(k7_lattice3(A_17)) | ~l1_orders_2(k7_lattice3(A_17)) | k7_lattice3(A_17)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_292, c_1902])).
% 20.29/9.83  tff(c_3790, plain, (![A_186]: (u1_orders_2(k7_lattice3(A_186))=u1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3(A_186)) | k7_lattice3(A_186)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_186) | ~l1_orders_2('#skF_1') | k7_lattice3(A_186)!=k7_lattice3('#skF_1') | ~l1_orders_2('#skF_1') | ~l1_orders_2(A_186))), inference(superposition, [status(thm), theory('equality')], [c_3730, c_1979])).
% 20.29/9.83  tff(c_29983, plain, (![A_333]: (u1_orders_2(k7_lattice3(A_333))=u1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3(A_333)) | k7_lattice3(A_333)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_333))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_3790])).
% 20.29/9.83  tff(c_30009, plain, (![A_17]: (u1_orders_2(k7_lattice3(A_17))=u1_orders_2(k7_lattice3('#skF_1')) | k7_lattice3(A_17)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_17))), inference(resolution, [status(thm)], [c_134, c_29983])).
% 20.29/9.83  tff(c_2658, plain, (![A_10, A_166]: (u1_orders_2(A_10)=k3_relset_1(u1_struct_0(A_166), u1_struct_0(A_166), u1_orders_2(A_166)) | k7_lattice3(A_166)!=A_10 | ~v1_orders_2(A_10) | ~l1_orders_2(A_166) | ~l1_orders_2(A_10))), inference(resolution, [status(thm)], [c_12, c_2617])).
% 20.29/9.83  tff(c_5470, plain, (![A_166]: (k3_relset_1(u1_struct_0(A_166), u1_struct_0(A_166), u1_orders_2(A_166))=u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | k7_lattice3(k7_lattice3('#skF_1'))!=k7_lattice3(A_166) | ~l1_orders_2(A_166) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_5422, c_2658])).
% 20.29/9.83  tff(c_47819, plain, (![A_435]: (k3_relset_1(u1_struct_0(A_435), u1_struct_0(A_435), u1_orders_2(A_435))=u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | k7_lattice3(k7_lattice3('#skF_1'))!=k7_lattice3(A_435) | ~l1_orders_2(A_435))), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_5470])).
% 20.29/9.83  tff(c_48020, plain, (![A_17]: (k3_relset_1(u1_struct_0(k7_lattice3('#skF_1')), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3(A_17)))=u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | ~l1_orders_2(k7_lattice3('#skF_1')) | k7_lattice3(A_17)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_17))), inference(superposition, [status(thm), theory('equality')], [c_30009, c_47819])).
% 20.29/9.83  tff(c_48130, plain, (![A_17]: (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_17)))=u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | k7_lattice3(A_17)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4053, c_4053, c_48020])).
% 20.29/9.83  tff(c_51725, plain, (u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))=u1_orders_2('#skF_1') | ~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51705, c_48130])).
% 20.29/9.83  tff(c_52046, plain, (u1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))=u1_orders_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_51725])).
% 20.29/9.83  tff(c_27291, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1')) | ~v1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))) | ~l1_orders_2(k7_lattice3(k7_lattice3('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_27089, c_6])).
% 20.29/9.83  tff(c_27452, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5421, c_5422, c_27291])).
% 20.29/9.83  tff(c_52432, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))=k7_lattice3(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52046, c_27452])).
% 20.29/9.83  tff(c_52434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_52432])).
% 20.29/9.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.29/9.83  
% 20.29/9.83  Inference rules
% 20.29/9.83  ----------------------
% 20.29/9.83  #Ref     : 26
% 20.29/9.83  #Sup     : 13966
% 20.29/9.83  #Fact    : 0
% 20.29/9.83  #Define  : 0
% 20.29/9.83  #Split   : 12
% 20.29/9.83  #Chain   : 0
% 20.29/9.83  #Close   : 0
% 20.29/9.83  
% 20.29/9.83  Ordering : KBO
% 20.29/9.83  
% 20.29/9.83  Simplification rules
% 20.29/9.83  ----------------------
% 20.29/9.83  #Subsume      : 2779
% 20.29/9.83  #Demod        : 16318
% 20.29/9.83  #Tautology    : 1995
% 20.29/9.83  #SimpNegUnit  : 55
% 20.29/9.83  #BackRed      : 40
% 20.29/9.83  
% 20.29/9.83  #Partial instantiations: 0
% 20.29/9.83  #Strategies tried      : 1
% 20.29/9.83  
% 20.29/9.83  Timing (in seconds)
% 20.29/9.83  ----------------------
% 20.29/9.83  Preprocessing        : 0.27
% 20.29/9.83  Parsing              : 0.15
% 20.29/9.83  CNF conversion       : 0.02
% 20.29/9.83  Main loop            : 8.75
% 20.29/9.83  Inferencing          : 1.69
% 20.29/9.83  Reduction            : 2.55
% 20.29/9.83  Demodulation         : 1.92
% 20.29/9.83  BG Simplification    : 0.33
% 20.29/9.83  Subsumption          : 3.73
% 20.29/9.83  Abstraction          : 0.47
% 20.29/9.83  MUC search           : 0.00
% 20.29/9.83  Cooper               : 0.00
% 20.29/9.83  Total                : 9.07
% 20.29/9.83  Index Insertion      : 0.00
% 20.29/9.83  Index Deletion       : 0.00
% 20.29/9.83  Index Matching       : 0.00
% 20.29/9.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
