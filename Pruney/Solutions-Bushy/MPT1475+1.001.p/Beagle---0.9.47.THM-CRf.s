%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1475+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:57 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :   82 (2873 expanded)
%              Number of leaves         :   21 ( 972 expanded)
%              Depth                    :   26
%              Number of atoms          :  200 (8529 expanded)
%              Number of equality atoms :   85 (3065 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,k3_relset_1(A,B,C)) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

tff(c_18,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_orders_2(k7_lattice3(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_2] :
      ( g1_orders_2(u1_struct_0(A_2),k3_relset_1(u1_struct_0(A_2),u1_struct_0(A_2),u1_orders_2(A_2))) = k7_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69,plain,(
    ! [D_26,B_27,C_28,A_29] :
      ( D_26 = B_27
      | g1_orders_2(C_28,D_26) != g1_orders_2(A_29,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    ! [A_47,D_48,C_49] :
      ( u1_orders_2(A_47) = D_48
      | g1_orders_2(C_49,D_48) != A_47
      | ~ m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ v1_orders_2(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_2003,plain,(
    ! [A_127,A_128] :
      ( u1_orders_2(A_127) = k3_relset_1(u1_struct_0(A_128),u1_struct_0(A_128),u1_orders_2(A_128))
      | k7_lattice3(A_128) != A_127
      | ~ m1_subset_1(u1_orders_2(A_127),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127),u1_struct_0(A_127))))
      | ~ v1_orders_2(A_127)
      | ~ l1_orders_2(A_127)
      | ~ l1_orders_2(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_2070,plain,(
    ! [A_129,A_130] :
      ( u1_orders_2(A_129) = k3_relset_1(u1_struct_0(A_130),u1_struct_0(A_130),u1_orders_2(A_130))
      | k7_lattice3(A_130) != A_129
      | ~ v1_orders_2(A_129)
      | ~ l1_orders_2(A_130)
      | ~ l1_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_10,c_2003])).

tff(c_2074,plain,(
    ! [A_131,A_132] :
      ( u1_orders_2(k7_lattice3(A_131)) = k3_relset_1(u1_struct_0(A_132),u1_struct_0(A_132),u1_orders_2(A_132))
      | k7_lattice3(A_132) != k7_lattice3(A_131)
      | ~ l1_orders_2(A_132)
      | ~ l1_orders_2(k7_lattice3(A_131))
      | ~ l1_orders_2(A_131) ) ),
    inference(resolution,[status(thm)],[c_8,c_2070])).

tff(c_2078,plain,(
    ! [A_133,A_134] :
      ( u1_orders_2(k7_lattice3(A_133)) = k3_relset_1(u1_struct_0(A_134),u1_struct_0(A_134),u1_orders_2(A_134))
      | k7_lattice3(A_134) != k7_lattice3(A_133)
      | ~ l1_orders_2(A_134)
      | ~ l1_orders_2(A_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_2074])).

tff(c_61,plain,(
    ! [A_23,B_24,C_25] :
      ( k3_relset_1(A_23,B_24,k3_relset_1(A_23,B_24,C_25)) = C_25
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_4] :
      ( k3_relset_1(u1_struct_0(A_4),u1_struct_0(A_4),k3_relset_1(u1_struct_0(A_4),u1_struct_0(A_4),u1_orders_2(A_4))) = u1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_2145,plain,(
    ! [A_134,A_133] :
      ( k3_relset_1(u1_struct_0(A_134),u1_struct_0(A_134),u1_orders_2(k7_lattice3(A_133))) = u1_orders_2(A_134)
      | ~ l1_orders_2(A_134)
      | k7_lattice3(A_134) != k7_lattice3(A_133)
      | ~ l1_orders_2(A_134)
      | ~ l1_orders_2(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2078,c_64])).

tff(c_52,plain,(
    ! [C_19,A_20,D_21,B_22] :
      ( C_19 = A_20
      | g1_orders_2(C_19,D_21) != g1_orders_2(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_31,A_32,B_33] :
      ( u1_struct_0(A_31) = A_32
      | k7_lattice3(A_31) != g1_orders_2(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ l1_orders_2(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_152,plain,(
    ! [A_54,A_53] :
      ( u1_struct_0(A_54) = u1_struct_0(A_53)
      | k7_lattice3(A_53) != A_54
      | ~ m1_subset_1(u1_orders_2(A_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(A_54))))
      | ~ l1_orders_2(A_53)
      | ~ v1_orders_2(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_157,plain,(
    ! [A_56,A_55] :
      ( u1_struct_0(A_56) = u1_struct_0(A_55)
      | k7_lattice3(A_55) != A_56
      | ~ l1_orders_2(A_55)
      | ~ v1_orders_2(A_56)
      | ~ l1_orders_2(A_56) ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_165,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = u1_struct_0('#skF_1')
      | k7_lattice3('#skF_1') != A_57
      | ~ v1_orders_2(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(resolution,[status(thm)],[c_20,c_157])).

tff(c_170,plain,(
    ! [A_58] :
      ( u1_struct_0(k7_lattice3(A_58)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_58) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(k7_lattice3(A_58))
      | ~ l1_orders_2(A_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_165])).

tff(c_174,plain,(
    ! [A_3] :
      ( u1_struct_0(k7_lattice3(A_3)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_3) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_180,plain,(
    ! [A_62] :
      ( u1_struct_0(k7_lattice3(A_62)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_62) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_369,plain,(
    ! [A_71] :
      ( m1_subset_1(u1_orders_2(k7_lattice3(A_71)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3(A_71)))))
      | ~ l1_orders_2(k7_lattice3(A_71))
      | k7_lattice3(A_71) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_10])).

tff(c_3514,plain,(
    ! [A_163] :
      ( m1_subset_1(u1_orders_2(k7_lattice3(A_163)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ l1_orders_2(k7_lattice3(A_163))
      | k7_lattice3(A_163) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_163)
      | k7_lattice3(A_163) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_369])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k3_relset_1(A_11,B_12,k3_relset_1(A_11,B_12,C_13)) = C_13
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3988,plain,(
    ! [A_171] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_171)))) = u1_orders_2(k7_lattice3(A_171))
      | ~ l1_orders_2(k7_lattice3(A_171))
      | k7_lattice3(A_171) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_171) ) ),
    inference(resolution,[status(thm)],[c_3514,c_16])).

tff(c_4004,plain,(
    ! [A_133] :
      ( u1_orders_2(k7_lattice3(A_133)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_133))
      | k7_lattice3(A_133) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_133)
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_133) != k7_lattice3('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | ~ l1_orders_2(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_3988])).

tff(c_4012,plain,(
    ! [A_172] :
      ( u1_orders_2(k7_lattice3(A_172)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | ~ l1_orders_2(k7_lattice3(A_172))
      | k7_lattice3(A_172) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_4004])).

tff(c_4016,plain,(
    ! [A_173] :
      ( u1_orders_2(k7_lattice3(A_173)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_4012])).

tff(c_4126,plain,(
    ! [A_173] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = u1_orders_2('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_64])).

tff(c_4164,plain,(
    ! [A_173] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = u1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4126])).

tff(c_4015,plain,(
    ! [A_3] :
      ( u1_orders_2(k7_lattice3(A_3)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | k7_lattice3(A_3) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_4012])).

tff(c_4132,plain,(
    ! [A_173] :
      ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = k7_lattice3('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_4])).

tff(c_4170,plain,(
    ! [A_174] :
      ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_174))) = k7_lattice3('#skF_1')
      | k7_lattice3(A_174) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4132])).

tff(c_4219,plain,(
    ! [A_3] :
      ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))) = k7_lattice3('#skF_1')
      | k7_lattice3(A_3) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_3)
      | k7_lattice3(A_3) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4015,c_4170])).

tff(c_5179,plain,(
    ! [A_199] :
      ( k7_lattice3(A_199) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_199)
      | k7_lattice3(A_199) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_199) ) ),
    inference(splitLeft,[status(thm)],[c_4219])).

tff(c_5183,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_5179])).

tff(c_5188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5183])).

tff(c_5189,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))) = k7_lattice3('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4219])).

tff(c_60,plain,(
    ! [A_1,C_19,D_21] :
      ( u1_struct_0(A_1) = C_19
      | g1_orders_2(C_19,D_21) != A_1
      | ~ m1_subset_1(u1_orders_2(A_1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(A_1))))
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_4248,plain,(
    ! [C_175,D_176] :
      ( u1_struct_0(g1_orders_2(C_175,D_176)) = C_175
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(C_175,D_176)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(C_175,D_176)),u1_struct_0(g1_orders_2(C_175,D_176)))))
      | ~ v1_orders_2(g1_orders_2(C_175,D_176))
      | ~ l1_orders_2(g1_orders_2(C_175,D_176)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_60])).

tff(c_4387,plain,(
    ! [C_175,D_176] :
      ( u1_struct_0(g1_orders_2(C_175,D_176)) = C_175
      | ~ v1_orders_2(g1_orders_2(C_175,D_176))
      | ~ l1_orders_2(g1_orders_2(C_175,D_176)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4248])).

tff(c_5193,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1')))) = u1_struct_0('#skF_1')
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5189,c_4387])).

tff(c_5237,plain,
    ( u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0('#skF_1')
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5189,c_5189,c_5193])).

tff(c_5249,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5237])).

tff(c_5252,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_5249])).

tff(c_5256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5252])).

tff(c_5258,plain,(
    l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5237])).

tff(c_5257,plain,
    ( ~ v1_orders_2(k7_lattice3('#skF_1'))
    | u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5237])).

tff(c_5267,plain,(
    ~ v1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5257])).

tff(c_5270,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_5267])).

tff(c_5274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5270])).

tff(c_5275,plain,(
    u1_struct_0(k7_lattice3('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5257])).

tff(c_198,plain,(
    ! [A_62] :
      ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0(k7_lattice3(A_62)),u1_struct_0(k7_lattice3(A_62)),u1_orders_2(k7_lattice3(A_62)))) = k7_lattice3(k7_lattice3(A_62))
      | ~ l1_orders_2(k7_lattice3(A_62))
      | k7_lattice3(A_62) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_4])).

tff(c_5324,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5275,c_198])).

tff(c_5503,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3('#skF_1')))) = k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5258,c_5275,c_5324])).

tff(c_6930,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) = k7_lattice3(k7_lattice3('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4164,c_5503])).

tff(c_6953,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) = k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6930])).

tff(c_6955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_6953])).

%------------------------------------------------------------------------------
