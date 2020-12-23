%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:39 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.11s
% Verified   : 
% Statistics : Number of formulae       :   84 (2873 expanded)
%              Number of leaves         :   21 ( 972 expanded)
%              Depth                    :   26
%              Number of atoms          :  205 (8529 expanded)
%              Number of equality atoms :   88 (3065 expanded)
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

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,k3_relset_1(A,B,C)) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

tff(c_18,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2('#skF_1')) != k7_lattice3(k7_lattice3('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13] :
      ( l1_orders_2(k7_lattice3(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_orders_2(k7_lattice3(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(u1_orders_2(A_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(A_5))))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_12] :
      ( g1_orders_2(u1_struct_0(A_12),k3_relset_1(u1_struct_0(A_12),u1_struct_0(A_12),u1_orders_2(A_12))) = k7_lattice3(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_4] :
      ( g1_orders_2(u1_struct_0(A_4),u1_orders_2(A_4)) = A_4
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [D_23,B_24,C_25,A_26] :
      ( D_23 = B_24
      | g1_orders_2(C_25,D_23) != g1_orders_2(A_26,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ! [A_44,D_45,C_46] :
      ( u1_orders_2(A_44) = D_45
      | g1_orders_2(C_46,D_45) != A_44
      | ~ m1_subset_1(u1_orders_2(A_44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44),u1_struct_0(A_44))))
      | ~ v1_orders_2(A_44)
      | ~ l1_orders_2(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_2003,plain,(
    ! [A_127,A_128] :
      ( u1_orders_2(A_127) = k3_relset_1(u1_struct_0(A_128),u1_struct_0(A_128),u1_orders_2(A_128))
      | k7_lattice3(A_128) != A_127
      | ~ m1_subset_1(u1_orders_2(A_127),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127),u1_struct_0(A_127))))
      | ~ v1_orders_2(A_127)
      | ~ l1_orders_2(A_127)
      | ~ l1_orders_2(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_2070,plain,(
    ! [A_129,A_130] :
      ( u1_orders_2(A_129) = k3_relset_1(u1_struct_0(A_130),u1_struct_0(A_130),u1_orders_2(A_130))
      | k7_lattice3(A_130) != A_129
      | ~ v1_orders_2(A_129)
      | ~ l1_orders_2(A_130)
      | ~ l1_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_6,c_2003])).

tff(c_2074,plain,(
    ! [A_131,A_132] :
      ( u1_orders_2(k7_lattice3(A_131)) = k3_relset_1(u1_struct_0(A_132),u1_struct_0(A_132),u1_orders_2(A_132))
      | k7_lattice3(A_132) != k7_lattice3(A_131)
      | ~ l1_orders_2(A_132)
      | ~ l1_orders_2(k7_lattice3(A_131))
      | ~ l1_orders_2(A_131) ) ),
    inference(resolution,[status(thm)],[c_16,c_2070])).

tff(c_2078,plain,(
    ! [A_133,A_134] :
      ( u1_orders_2(k7_lattice3(A_133)) = k3_relset_1(u1_struct_0(A_134),u1_struct_0(A_134),u1_orders_2(A_134))
      | k7_lattice3(A_134) != k7_lattice3(A_133)
      | ~ l1_orders_2(A_134)
      | ~ l1_orders_2(A_133) ) ),
    inference(resolution,[status(thm)],[c_14,c_2074])).

tff(c_74,plain,(
    ! [A_27,B_28,C_29] :
      ( k3_relset_1(A_27,B_28,k3_relset_1(A_27,B_28,C_29)) = C_29
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_5] :
      ( k3_relset_1(u1_struct_0(A_5),u1_struct_0(A_5),k3_relset_1(u1_struct_0(A_5),u1_struct_0(A_5),u1_orders_2(A_5))) = u1_orders_2(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_2145,plain,(
    ! [A_134,A_133] :
      ( k3_relset_1(u1_struct_0(A_134),u1_struct_0(A_134),u1_orders_2(k7_lattice3(A_133))) = u1_orders_2(A_134)
      | ~ l1_orders_2(A_134)
      | k7_lattice3(A_134) != k7_lattice3(A_133)
      | ~ l1_orders_2(A_134)
      | ~ l1_orders_2(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2078,c_77])).

tff(c_48,plain,(
    ! [A_22] :
      ( g1_orders_2(u1_struct_0(A_22),k3_relset_1(u1_struct_0(A_22),u1_struct_0(A_22),u1_orders_2(A_22))) = k7_lattice3(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [C_10,A_6,D_11,B_7] :
      ( C_10 = A_6
      | g1_orders_2(C_10,D_11) != g1_orders_2(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k2_zfmisc_1(A_6,A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [A_30,A_31,B_32] :
      ( u1_struct_0(A_30) = A_31
      | k7_lattice3(A_30) != g1_orders_2(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ l1_orders_2(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_152,plain,(
    ! [A_54,A_53] :
      ( u1_struct_0(A_54) = u1_struct_0(A_53)
      | k7_lattice3(A_54) != A_53
      | ~ m1_subset_1(u1_orders_2(A_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_53),u1_struct_0(A_53))))
      | ~ l1_orders_2(A_54)
      | ~ v1_orders_2(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_157,plain,(
    ! [A_56,A_55] :
      ( u1_struct_0(A_56) = u1_struct_0(A_55)
      | k7_lattice3(A_55) != A_56
      | ~ l1_orders_2(A_55)
      | ~ v1_orders_2(A_56)
      | ~ l1_orders_2(A_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

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
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_174,plain,(
    ! [A_13] :
      ( u1_struct_0(k7_lattice3(A_13)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_13) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_180,plain,(
    ! [A_62] :
      ( u1_struct_0(k7_lattice3(A_62)) = u1_struct_0('#skF_1')
      | k7_lattice3(A_62) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_369,plain,(
    ! [A_71] :
      ( m1_subset_1(u1_orders_2(k7_lattice3(A_71)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(k7_lattice3(A_71)))))
      | ~ l1_orders_2(k7_lattice3(A_71))
      | k7_lattice3(A_71) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_6])).

tff(c_3514,plain,(
    ! [A_163] :
      ( m1_subset_1(u1_orders_2(k7_lattice3(A_163)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ l1_orders_2(k7_lattice3(A_163))
      | k7_lattice3(A_163) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_163)
      | k7_lattice3(A_163) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_369])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k3_relset_1(A_1,B_2,k3_relset_1(A_1,B_2,C_3)) = C_3
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3988,plain,(
    ! [A_171] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_171)))) = u1_orders_2(k7_lattice3(A_171))
      | ~ l1_orders_2(k7_lattice3(A_171))
      | k7_lattice3(A_171) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_171) ) ),
    inference(resolution,[status(thm)],[c_3514,c_2])).

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
    inference(resolution,[status(thm)],[c_14,c_4012])).

tff(c_4126,plain,(
    ! [A_173] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = u1_orders_2('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_77])).

tff(c_4164,plain,(
    ! [A_173] :
      ( k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = u1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4126])).

tff(c_4015,plain,(
    ! [A_13] :
      ( u1_orders_2(k7_lattice3(A_13)) = k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))
      | k7_lattice3(A_13) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_4012])).

tff(c_4132,plain,(
    ! [A_173] :
      ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_173))) = k7_lattice3('#skF_1')
      | ~ l1_orders_2('#skF_1')
      | k7_lattice3(A_173) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_12])).

tff(c_4170,plain,(
    ! [A_174] :
      ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k7_lattice3(A_174))) = k7_lattice3('#skF_1')
      | k7_lattice3(A_174) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4132])).

tff(c_4219,plain,(
    ! [A_13] :
      ( g1_orders_2(u1_struct_0('#skF_1'),k3_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_orders_2('#skF_1'))) = k7_lattice3('#skF_1')
      | k7_lattice3(A_13) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_13)
      | k7_lattice3(A_13) != k7_lattice3('#skF_1')
      | ~ l1_orders_2(A_13) ) ),
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

tff(c_43,plain,(
    ! [C_18,A_19,D_20,B_21] :
      ( C_18 = A_19
      | g1_orders_2(C_18,D_20) != g1_orders_2(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    ! [A_4,C_18,D_20] :
      ( u1_struct_0(A_4) = C_18
      | g1_orders_2(C_18,D_20) != A_4
      | ~ m1_subset_1(u1_orders_2(A_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4),u1_struct_0(A_4))))
      | ~ v1_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_4248,plain,(
    ! [C_175,D_176] :
      ( u1_struct_0(g1_orders_2(C_175,D_176)) = C_175
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(C_175,D_176)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(C_175,D_176)),u1_struct_0(g1_orders_2(C_175,D_176)))))
      | ~ v1_orders_2(g1_orders_2(C_175,D_176))
      | ~ l1_orders_2(g1_orders_2(C_175,D_176)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_47])).

tff(c_4387,plain,(
    ! [C_175,D_176] :
      ( u1_struct_0(g1_orders_2(C_175,D_176)) = C_175
      | ~ v1_orders_2(g1_orders_2(C_175,D_176))
      | ~ l1_orders_2(g1_orders_2(C_175,D_176)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4248])).

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
    inference(resolution,[status(thm)],[c_14,c_5249])).

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
    inference(resolution,[status(thm)],[c_16,c_5267])).

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
    inference(superposition,[status(thm),theory(equality)],[c_180,c_12])).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.11/2.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.11/2.78  
% 8.11/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.11/2.78  %$ m1_subset_1 > v1_orders_2 > l1_orders_2 > k3_relset_1 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k1_zfmisc_1 > #skF_1
% 8.11/2.78  
% 8.11/2.78  %Foreground sorts:
% 8.11/2.78  
% 8.11/2.78  
% 8.11/2.78  %Background operators:
% 8.11/2.78  
% 8.11/2.78  
% 8.11/2.78  %Foreground operators:
% 8.11/2.78  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 8.11/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.11/2.78  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.11/2.78  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 8.11/2.78  tff(k7_lattice3, type, k7_lattice3: $i > $i).
% 8.11/2.78  tff('#skF_1', type, '#skF_1': $i).
% 8.11/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.11/2.78  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.11/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.11/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.11/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.11/2.78  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 8.11/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.11/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.11/2.78  
% 8.11/2.80  tff(f_63, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k7_lattice3(k7_lattice3(A)) = g1_orders_2(u1_struct_0(A), u1_orders_2(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_lattice3)).
% 8.11/2.80  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(k7_lattice3(A)) & l1_orders_2(k7_lattice3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_lattice3)).
% 8.11/2.80  tff(f_39, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 8.11/2.80  tff(f_52, axiom, (![A]: (l1_orders_2(A) => (k7_lattice3(A) = g1_orders_2(u1_struct_0(A), k3_relset_1(u1_struct_0(A), u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattice3)).
% 8.11/2.80  tff(f_35, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 8.11/2.80  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 8.11/2.80  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, k3_relset_1(A, B, C)) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_relset_1)).
% 8.11/2.80  tff(c_18, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))!=k7_lattice3(k7_lattice3('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.11/2.80  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.11/2.80  tff(c_14, plain, (![A_13]: (l1_orders_2(k7_lattice3(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.11/2.80  tff(c_16, plain, (![A_13]: (v1_orders_2(k7_lattice3(A_13)) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.11/2.80  tff(c_6, plain, (![A_5]: (m1_subset_1(u1_orders_2(A_5), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5), u1_struct_0(A_5)))) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.11/2.80  tff(c_12, plain, (![A_12]: (g1_orders_2(u1_struct_0(A_12), k3_relset_1(u1_struct_0(A_12), u1_struct_0(A_12), u1_orders_2(A_12)))=k7_lattice3(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.11/2.80  tff(c_4, plain, (![A_4]: (g1_orders_2(u1_struct_0(A_4), u1_orders_2(A_4))=A_4 | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.11/2.80  tff(c_65, plain, (![D_23, B_24, C_25, A_26]: (D_23=B_24 | g1_orders_2(C_25, D_23)!=g1_orders_2(A_26, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.11/2.80  tff(c_128, plain, (![A_44, D_45, C_46]: (u1_orders_2(A_44)=D_45 | g1_orders_2(C_46, D_45)!=A_44 | ~m1_subset_1(u1_orders_2(A_44), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_44), u1_struct_0(A_44)))) | ~v1_orders_2(A_44) | ~l1_orders_2(A_44))), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 8.11/2.80  tff(c_2003, plain, (![A_127, A_128]: (u1_orders_2(A_127)=k3_relset_1(u1_struct_0(A_128), u1_struct_0(A_128), u1_orders_2(A_128)) | k7_lattice3(A_128)!=A_127 | ~m1_subset_1(u1_orders_2(A_127), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_127), u1_struct_0(A_127)))) | ~v1_orders_2(A_127) | ~l1_orders_2(A_127) | ~l1_orders_2(A_128))), inference(superposition, [status(thm), theory('equality')], [c_12, c_128])).
% 8.11/2.80  tff(c_2070, plain, (![A_129, A_130]: (u1_orders_2(A_129)=k3_relset_1(u1_struct_0(A_130), u1_struct_0(A_130), u1_orders_2(A_130)) | k7_lattice3(A_130)!=A_129 | ~v1_orders_2(A_129) | ~l1_orders_2(A_130) | ~l1_orders_2(A_129))), inference(resolution, [status(thm)], [c_6, c_2003])).
% 8.11/2.80  tff(c_2074, plain, (![A_131, A_132]: (u1_orders_2(k7_lattice3(A_131))=k3_relset_1(u1_struct_0(A_132), u1_struct_0(A_132), u1_orders_2(A_132)) | k7_lattice3(A_132)!=k7_lattice3(A_131) | ~l1_orders_2(A_132) | ~l1_orders_2(k7_lattice3(A_131)) | ~l1_orders_2(A_131))), inference(resolution, [status(thm)], [c_16, c_2070])).
% 8.11/2.80  tff(c_2078, plain, (![A_133, A_134]: (u1_orders_2(k7_lattice3(A_133))=k3_relset_1(u1_struct_0(A_134), u1_struct_0(A_134), u1_orders_2(A_134)) | k7_lattice3(A_134)!=k7_lattice3(A_133) | ~l1_orders_2(A_134) | ~l1_orders_2(A_133))), inference(resolution, [status(thm)], [c_14, c_2074])).
% 8.11/2.80  tff(c_74, plain, (![A_27, B_28, C_29]: (k3_relset_1(A_27, B_28, k3_relset_1(A_27, B_28, C_29))=C_29 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.11/2.80  tff(c_77, plain, (![A_5]: (k3_relset_1(u1_struct_0(A_5), u1_struct_0(A_5), k3_relset_1(u1_struct_0(A_5), u1_struct_0(A_5), u1_orders_2(A_5)))=u1_orders_2(A_5) | ~l1_orders_2(A_5))), inference(resolution, [status(thm)], [c_6, c_74])).
% 8.11/2.80  tff(c_2145, plain, (![A_134, A_133]: (k3_relset_1(u1_struct_0(A_134), u1_struct_0(A_134), u1_orders_2(k7_lattice3(A_133)))=u1_orders_2(A_134) | ~l1_orders_2(A_134) | k7_lattice3(A_134)!=k7_lattice3(A_133) | ~l1_orders_2(A_134) | ~l1_orders_2(A_133))), inference(superposition, [status(thm), theory('equality')], [c_2078, c_77])).
% 8.11/2.80  tff(c_48, plain, (![A_22]: (g1_orders_2(u1_struct_0(A_22), k3_relset_1(u1_struct_0(A_22), u1_struct_0(A_22), u1_orders_2(A_22)))=k7_lattice3(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.11/2.80  tff(c_10, plain, (![C_10, A_6, D_11, B_7]: (C_10=A_6 | g1_orders_2(C_10, D_11)!=g1_orders_2(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(k2_zfmisc_1(A_6, A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.11/2.80  tff(c_78, plain, (![A_30, A_31, B_32]: (u1_struct_0(A_30)=A_31 | k7_lattice3(A_30)!=g1_orders_2(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~l1_orders_2(A_30))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 8.11/2.80  tff(c_152, plain, (![A_54, A_53]: (u1_struct_0(A_54)=u1_struct_0(A_53) | k7_lattice3(A_54)!=A_53 | ~m1_subset_1(u1_orders_2(A_53), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_53), u1_struct_0(A_53)))) | ~l1_orders_2(A_54) | ~v1_orders_2(A_53) | ~l1_orders_2(A_53))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78])).
% 8.11/2.80  tff(c_157, plain, (![A_56, A_55]: (u1_struct_0(A_56)=u1_struct_0(A_55) | k7_lattice3(A_55)!=A_56 | ~l1_orders_2(A_55) | ~v1_orders_2(A_56) | ~l1_orders_2(A_56))), inference(resolution, [status(thm)], [c_6, c_152])).
% 8.11/2.80  tff(c_165, plain, (![A_57]: (u1_struct_0(A_57)=u1_struct_0('#skF_1') | k7_lattice3('#skF_1')!=A_57 | ~v1_orders_2(A_57) | ~l1_orders_2(A_57))), inference(resolution, [status(thm)], [c_20, c_157])).
% 8.11/2.80  tff(c_170, plain, (![A_58]: (u1_struct_0(k7_lattice3(A_58))=u1_struct_0('#skF_1') | k7_lattice3(A_58)!=k7_lattice3('#skF_1') | ~l1_orders_2(k7_lattice3(A_58)) | ~l1_orders_2(A_58))), inference(resolution, [status(thm)], [c_16, c_165])).
% 8.11/2.80  tff(c_174, plain, (![A_13]: (u1_struct_0(k7_lattice3(A_13))=u1_struct_0('#skF_1') | k7_lattice3(A_13)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_13))), inference(resolution, [status(thm)], [c_14, c_170])).
% 8.11/2.80  tff(c_180, plain, (![A_62]: (u1_struct_0(k7_lattice3(A_62))=u1_struct_0('#skF_1') | k7_lattice3(A_62)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_62))), inference(resolution, [status(thm)], [c_14, c_170])).
% 8.11/2.80  tff(c_369, plain, (![A_71]: (m1_subset_1(u1_orders_2(k7_lattice3(A_71)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(k7_lattice3(A_71))))) | ~l1_orders_2(k7_lattice3(A_71)) | k7_lattice3(A_71)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_71))), inference(superposition, [status(thm), theory('equality')], [c_180, c_6])).
% 8.11/2.80  tff(c_3514, plain, (![A_163]: (m1_subset_1(u1_orders_2(k7_lattice3(A_163)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1')))) | ~l1_orders_2(k7_lattice3(A_163)) | k7_lattice3(A_163)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_163) | k7_lattice3(A_163)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_163))), inference(superposition, [status(thm), theory('equality')], [c_174, c_369])).
% 8.11/2.80  tff(c_2, plain, (![A_1, B_2, C_3]: (k3_relset_1(A_1, B_2, k3_relset_1(A_1, B_2, C_3))=C_3 | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.11/2.80  tff(c_3988, plain, (![A_171]: (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_171))))=u1_orders_2(k7_lattice3(A_171)) | ~l1_orders_2(k7_lattice3(A_171)) | k7_lattice3(A_171)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_171))), inference(resolution, [status(thm)], [c_3514, c_2])).
% 8.11/2.80  tff(c_4004, plain, (![A_133]: (u1_orders_2(k7_lattice3(A_133))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | ~l1_orders_2(k7_lattice3(A_133)) | k7_lattice3(A_133)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_133) | ~l1_orders_2('#skF_1') | k7_lattice3(A_133)!=k7_lattice3('#skF_1') | ~l1_orders_2('#skF_1') | ~l1_orders_2(A_133))), inference(superposition, [status(thm), theory('equality')], [c_2145, c_3988])).
% 8.11/2.80  tff(c_4012, plain, (![A_172]: (u1_orders_2(k7_lattice3(A_172))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | ~l1_orders_2(k7_lattice3(A_172)) | k7_lattice3(A_172)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_172))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_4004])).
% 8.11/2.80  tff(c_4016, plain, (![A_173]: (u1_orders_2(k7_lattice3(A_173))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | k7_lattice3(A_173)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_173))), inference(resolution, [status(thm)], [c_14, c_4012])).
% 8.11/2.80  tff(c_4126, plain, (![A_173]: (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_173)))=u1_orders_2('#skF_1') | ~l1_orders_2('#skF_1') | k7_lattice3(A_173)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_173))), inference(superposition, [status(thm), theory('equality')], [c_4016, c_77])).
% 8.11/2.80  tff(c_4164, plain, (![A_173]: (k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_173)))=u1_orders_2('#skF_1') | k7_lattice3(A_173)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4126])).
% 8.11/2.80  tff(c_4015, plain, (![A_13]: (u1_orders_2(k7_lattice3(A_13))=k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')) | k7_lattice3(A_13)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_13))), inference(resolution, [status(thm)], [c_14, c_4012])).
% 8.11/2.80  tff(c_4132, plain, (![A_173]: (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_173)))=k7_lattice3('#skF_1') | ~l1_orders_2('#skF_1') | k7_lattice3(A_173)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_173))), inference(superposition, [status(thm), theory('equality')], [c_4016, c_12])).
% 8.11/2.80  tff(c_4170, plain, (![A_174]: (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3(A_174)))=k7_lattice3('#skF_1') | k7_lattice3(A_174)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4132])).
% 8.11/2.80  tff(c_4219, plain, (![A_13]: (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')))=k7_lattice3('#skF_1') | k7_lattice3(A_13)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_13) | k7_lattice3(A_13)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_13))), inference(superposition, [status(thm), theory('equality')], [c_4015, c_4170])).
% 8.11/2.80  tff(c_5179, plain, (![A_199]: (k7_lattice3(A_199)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_199) | k7_lattice3(A_199)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_199))), inference(splitLeft, [status(thm)], [c_4219])).
% 8.11/2.80  tff(c_5183, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_20, c_5179])).
% 8.11/2.80  tff(c_5188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_5183])).
% 8.11/2.80  tff(c_5189, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1')))=k7_lattice3('#skF_1')), inference(splitRight, [status(thm)], [c_4219])).
% 8.11/2.80  tff(c_43, plain, (![C_18, A_19, D_20, B_21]: (C_18=A_19 | g1_orders_2(C_18, D_20)!=g1_orders_2(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.11/2.80  tff(c_47, plain, (![A_4, C_18, D_20]: (u1_struct_0(A_4)=C_18 | g1_orders_2(C_18, D_20)!=A_4 | ~m1_subset_1(u1_orders_2(A_4), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4), u1_struct_0(A_4)))) | ~v1_orders_2(A_4) | ~l1_orders_2(A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_43])).
% 8.11/2.80  tff(c_4248, plain, (![C_175, D_176]: (u1_struct_0(g1_orders_2(C_175, D_176))=C_175 | ~m1_subset_1(u1_orders_2(g1_orders_2(C_175, D_176)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(C_175, D_176)), u1_struct_0(g1_orders_2(C_175, D_176))))) | ~v1_orders_2(g1_orders_2(C_175, D_176)) | ~l1_orders_2(g1_orders_2(C_175, D_176)))), inference(reflexivity, [status(thm), theory('equality')], [c_47])).
% 8.11/2.80  tff(c_4387, plain, (![C_175, D_176]: (u1_struct_0(g1_orders_2(C_175, D_176))=C_175 | ~v1_orders_2(g1_orders_2(C_175, D_176)) | ~l1_orders_2(g1_orders_2(C_175, D_176)))), inference(resolution, [status(thm)], [c_6, c_4248])).
% 8.11/2.80  tff(c_5193, plain, (u1_struct_0(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))))=u1_struct_0('#skF_1') | ~v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_5189, c_4387])).
% 8.11/2.80  tff(c_5237, plain, (u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0('#skF_1') | ~v1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5189, c_5189, c_5193])).
% 8.11/2.80  tff(c_5249, plain, (~l1_orders_2(k7_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_5237])).
% 8.11/2.80  tff(c_5252, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_14, c_5249])).
% 8.11/2.80  tff(c_5256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_5252])).
% 8.11/2.80  tff(c_5258, plain, (l1_orders_2(k7_lattice3('#skF_1'))), inference(splitRight, [status(thm)], [c_5237])).
% 8.11/2.80  tff(c_5257, plain, (~v1_orders_2(k7_lattice3('#skF_1')) | u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_5237])).
% 8.11/2.80  tff(c_5267, plain, (~v1_orders_2(k7_lattice3('#skF_1'))), inference(splitLeft, [status(thm)], [c_5257])).
% 8.11/2.80  tff(c_5270, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_16, c_5267])).
% 8.11/2.80  tff(c_5274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_5270])).
% 8.11/2.80  tff(c_5275, plain, (u1_struct_0(k7_lattice3('#skF_1'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_5257])).
% 8.11/2.80  tff(c_198, plain, (![A_62]: (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0(k7_lattice3(A_62)), u1_struct_0(k7_lattice3(A_62)), u1_orders_2(k7_lattice3(A_62))))=k7_lattice3(k7_lattice3(A_62)) | ~l1_orders_2(k7_lattice3(A_62)) | k7_lattice3(A_62)!=k7_lattice3('#skF_1') | ~l1_orders_2(A_62))), inference(superposition, [status(thm), theory('equality')], [c_180, c_12])).
% 8.11/2.80  tff(c_5324, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0(k7_lattice3('#skF_1')), u1_orders_2(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1')) | ~l1_orders_2(k7_lattice3('#skF_1')) | ~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5275, c_198])).
% 8.11/2.80  tff(c_5503, plain, (g1_orders_2(u1_struct_0('#skF_1'), k3_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_1'), u1_orders_2(k7_lattice3('#skF_1'))))=k7_lattice3(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5258, c_5275, c_5324])).
% 8.11/2.80  tff(c_6930, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))=k7_lattice3(k7_lattice3('#skF_1')) | ~l1_orders_2('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4164, c_5503])).
% 8.11/2.80  tff(c_6953, plain, (g1_orders_2(u1_struct_0('#skF_1'), u1_orders_2('#skF_1'))=k7_lattice3(k7_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6930])).
% 8.11/2.80  tff(c_6955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_6953])).
% 8.11/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.11/2.80  
% 8.11/2.80  Inference rules
% 8.11/2.80  ----------------------
% 8.11/2.80  #Ref     : 17
% 8.11/2.80  #Sup     : 2187
% 8.11/2.80  #Fact    : 0
% 8.11/2.80  #Define  : 0
% 8.11/2.80  #Split   : 5
% 8.11/2.80  #Chain   : 0
% 8.11/2.80  #Close   : 0
% 8.11/2.80  
% 8.11/2.80  Ordering : KBO
% 8.11/2.80  
% 8.11/2.80  Simplification rules
% 8.11/2.80  ----------------------
% 8.11/2.80  #Subsume      : 275
% 8.11/2.80  #Demod        : 438
% 8.11/2.80  #Tautology    : 180
% 8.11/2.80  #SimpNegUnit  : 1
% 8.11/2.80  #BackRed      : 0
% 8.11/2.80  
% 8.11/2.80  #Partial instantiations: 0
% 8.11/2.80  #Strategies tried      : 1
% 8.11/2.80  
% 8.11/2.80  Timing (in seconds)
% 8.11/2.80  ----------------------
% 8.11/2.80  Preprocessing        : 0.28
% 8.11/2.80  Parsing              : 0.16
% 8.11/2.80  CNF conversion       : 0.02
% 8.11/2.80  Main loop            : 1.71
% 8.11/2.80  Inferencing          : 0.51
% 8.11/2.80  Reduction            : 0.42
% 8.11/2.80  Demodulation         : 0.28
% 8.11/2.80  BG Simplification    : 0.11
% 8.11/2.80  Subsumption          : 0.57
% 8.11/2.80  Abstraction          : 0.11
% 8.11/2.80  MUC search           : 0.00
% 8.11/2.80  Cooper               : 0.00
% 8.11/2.80  Total                : 2.03
% 8.11/2.81  Index Insertion      : 0.00
% 8.11/2.81  Index Deletion       : 0.00
% 8.11/2.81  Index Matching       : 0.00
% 8.11/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
